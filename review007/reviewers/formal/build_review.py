from pathlib import Path
import os, sys, re, json, hashlib, subprocess, resource, time, shutil

BASE=Path(__file__).resolve().parent
FROZEN=BASE.parents[1]/'frozen006'
SOURCE=FROZEN/'sources/submission001/lean'
PROJECT=Path('deps-project')
TC=Path('lean-runtime')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name, data): (BASE/name).write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,16*1024**3))
    resource.setrlimit(resource.RLIMIT_CPU,(180,181))
def command(label,args,cwd=None,env=None,wall=240):
    start=time.time(); d={'label':label,'argv':list(map(str,args)),'cwd':str(cwd or BASE),'wall_limit_sec':wall,'cpu_limit_sec':[180,181],'address_space_bytes':16*1024**3}
    try:
        p=subprocess.run(args,cwd=cwd or BASE,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=wall,preexec_fn=limits)
        d.update(returncode=p.returncode,stdout=p.stdout,stderr=p.stderr)
    except subprocess.TimeoutExpired as e:
        d.update(returncode=None,timeout=True,stdout=(e.stdout or b'').decode() if isinstance(e.stdout,bytes) else e.stdout,stderr=(e.stderr or b'').decode() if isinstance(e.stderr,bytes) else e.stderr)
    d['elapsed_sec']=time.time()-start
    (BASE/'logs').mkdir(exist_ok=True)
    save('logs/'+label+'.json',d)
    (BASE/'logs'/f'{label}.stdout.txt').write_text(d.get('stdout') or '')
    (BASE/'logs'/f'{label}.stderr.txt').write_text(d.get('stderr') or '')
    return d

if len(sys.argv)>1 and sys.argv[1]=='prepare':
    local={str(p.relative_to(SOURCE)).removesuffix('.lean').replace('/','.'):p for p in SOURCE.rglob('*.lean')}
    imports={m:re.findall(r'^import\s+([^\n]+)',p.read_text(),re.M) for m,p in local.items()}
    imports={m:[w for line in lines for w in line.split()] for m,lines in imports.items()}
    roots=['Submission.EFamily','Submission.Connections','Submission.SixMixFinite']
    order=[]; seen=set(); ext=set()
    def visit(m):
        if m in seen:return
        seen.add(m)
        if m not in local:ext.add(m);return
        assert 'Reject' not in m
        for dep in imports[m]:visit(dep)
        order.append(m)
    for m in roots:visit(m)
    save('LOCAL_IMPORT_DAG.json',{'roots':roots,'order':order,'local_edges':{m:imports[m] for m in order},'external_import_roots':sorted(ext),'source_hashes':{m:sha(local[m]) for m in order},'not_author_build_order':True})
    for m in order:
        dest=BASE/'src'/local[m].relative_to(SOURCE);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(local[m],dest)
    manifest=json.loads((PROJECT/'lake-manifest.json').read_text())
    pkgs=[]; caches=[]
    for p in manifest['packages']:
        root=PROJECT/'.lake/packages'/p['name']
        head=command('pin_'+p['name'],['git','--no-optional-locks','-C',str(root),'rev-parse','HEAD'])
        clean=command('status_'+p['name'],['git','--no-optional-locks','-C',str(root),'status','--porcelain','--untracked-files=no'])
        cache=root/'.lake/build/lib/lean'
        if cache.exists():caches.append(str(cache))
        pkgs.append({'name':p['name'],'pin':p.get('rev'),'head':head['stdout'].strip(),'tracked_status':clean['stdout'],'cache_exists':cache.exists(),'cache':str(cache)})
    save('RUNTIME_PINS.json',{'toolchain':(SOURCE/'lean-toolchain').read_text().strip(),'manifest_sha256':sha(SOURCE/'lake-manifest.json'),'existing_manifest_sha256':sha(PROJECT/'lake-manifest.json'),'manifest_equal':(SOURCE/'lake-manifest.json').read_bytes()==(PROJECT/'lake-manifest.json').read_bytes(),'packages':pkgs,'trust_boundary':'External package compiled objects and existing Lean runtime are reused; no full external source rebuild or provenance certification of cached binaries.'})
    command('lean_version',[str(TC/'bin/lean'),'--version'])
    command('project_root',['git','--no-optional-locks','-C',str(PROJECT),'rev-parse','--show-toplevel'])
    command('project_branch',['git','--no-optional-locks','-C',str(PROJECT),'branch','--show-current'])
    command('project_head',['git','--no-optional-locks','-C',str(PROJECT),'rev-parse','HEAD'])
    command('project_status',['git','--no-optional-locks','-C',str(PROJECT),'status','--short','--branch'])
    save('BUILD_ENV.json',{'LEAN_PATH':os.pathsep.join([str(BASE/'lib')]+caches+[str(TC/'lib/lean')]),'LEAN_BIN':str(TC/'bin/lean'),'lean_binary_sha256':sha(TC/'bin/lean'),'leanchecker_binary_sha256':sha(TC/'bin/leanchecker'),'options':['-j1','-M4096'],'limits':{'wall_sec':240,'cpu_sec':[180,181],'address_space_bytes':16*1024**3}})
    print(json.dumps({'local_modules':len(order),'order':order,'external_roots':sorted(ext),'pins_match':all(p['pin']==p['head'] for p in pkgs),'tracked_clean':all(not p['tracked_status'] for p in pkgs)}))
elif len(sys.argv)>1 and sys.argv[1]=='build':
    data=json.loads((BASE/'LOCAL_IMPORT_DAG.json').read_text()); settings=json.loads((BASE/'BUILD_ENV.json').read_text())
    env=os.environ.copy();env['LEAN_PATH']=settings['LEAN_PATH']
    results=[]
    for i,m in enumerate(data['order']):
        rel=m.replace('.','/')
        out=BASE/'lib'/f'{rel}.olean';out.parent.mkdir(parents=True,exist_ok=True)
        d=command(f'build_{i:02}_{m}',[settings['LEAN_BIN'],'-j1','-M4096','-o',str(out),rel+'.lean'],BASE/'src',env)
        results.append({'module':m,'returncode':d['returncode'],'elapsed_sec':d['elapsed_sec'],'source_sha256':sha(BASE/'src'/f'{rel}.lean'),'olean_sha256':sha(out) if out.exists() else None})
        save('BUILD_RESULT.json',{'results':results,'complete':len(results)==len(data['order']),'all_pass':all(r['returncode']==0 for r in results)})
        print(m,d['returncode'],round(d['elapsed_sec'],2),flush=True)
        if d['returncode']!=0: break
