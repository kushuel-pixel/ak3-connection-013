#!/usr/bin/env python3
"""Compose the fixed review007 Lean checks for candidate008. No dependency install.

This entry is intentionally limited to the source/fixture hashes reviewed in007.
All writes go to one new external directory supplied with --output.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys,importlib.util,difflib

PACK=Path(__file__).resolve().parents[1]
SRC=PACK/'sources/submission001/lean'
REVIEW=PACK/'review007/reviewers/formal'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def require(ok,why):
    if not ok:raise RuntimeError(why)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--runtime',type=Path,required=True)
    ap.add_argument('--deps-project',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--kernel',action='store_true',help='also replay the three selected modules with the same kernel')
    args=ap.parse_args();tc=args.runtime.resolve();project=args.deps_project.resolve();out=args.output.resolve()
    require(not out.exists(),'create-only output already exists')
    require(not any(out.is_relative_to(p) for p in [PACK,tc,project]),'output must be outside packet, runtime and dependency project')
    require((tc/'bin/lean').is_file(),'fixed direct Lean binary not found; no installation attempted')
    version=subprocess.check_output([str(tc/'bin/lean'),'--version'],text=True).strip()
    require('4.35.0' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version,'unexpected runtime version')
    require((SRC/'lake-manifest.json').read_bytes()==(project/'lake-manifest.json').read_bytes(),'dependency manifest bytes differ')
    lock=json.loads((SRC/'lake-manifest.json').read_text())
    dag=json.loads((REVIEW/'LOCAL_IMPORT_DAG.json').read_text())
    require(len(dag['order'])==31,'unexpected reviewed local closure')
    for name,sha in dag['source_hashes'].items():
        require(H(SRC/(name.replace('.','/')+'.lean'))==sha,'reviewed source hash mismatch: '+name)
    seal=json.loads((REVIEW/'FINAL_SEAL.json').read_text())['file_sha256']
    fixture_names=['ReviewerTypes','ReviewerSemantics','RejectWrongEndpoint','RejectWrongLength','RejectMissingUnit','RejectWitnessFromIff','RejectReversedMatrix','RejectFalseFiniteCount']
    for n in fixture_names:
        rel='src/'+n+'.lean'
        require(H(REVIEW/rel)==seal[rel],'reviewed fixture hash mismatch: '+n)
    # The public backend replaces two machine-specific defaults. Both are bound to CLI paths below.
    require(seal['build_review.py']=='30d4d21c7a0da03c3aab5e7be04c6f5d36580988b164ef40f76a6ea380489a53','reviewed backend identity mismatch')
    require(H(REVIEW/'build_review.py')=='2dfd5efd4f3f5c6450a9f7b67c29f2f31e69b3f6ebd3dec6ae285b6b15185a64','public backend hash mismatch')
    pins=[]
    for p in lock['packages']:
        path=project/'.lake/packages'/p['name']
        head=subprocess.check_output(['git','--no-optional-locks','-C',str(path),'rev-parse','HEAD'],text=True).strip()
        dirty=subprocess.check_output(['git','--no-optional-locks','-C',str(path),'status','--porcelain','--untracked-files=no'],text=True)
        require(head==p['rev'] and not dirty,'dependency pin or tracked state mismatch: '+p['name'])
        pins.append({'name':p['name'],'rev':head,'tracked_clean':True})
    out.mkdir(parents=True,exist_ok=False)
    def save(n,d):
        p=out/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
    save('ADMISSION.json',{'runtime':version,'runtime_path':str(tc),'dependency_project':str(project),'packages':pins,'reviewed_source_count':31,'source_unchanged':True,'scope':'candidate008 portable composition, not new independent review'})
    original=(REVIEW/'build_review.py').read_text();backend=original
    changes={"BASE=Path(__file__).resolve().parent":"BASE=Path("+repr(str(out))+")",
             "SOURCE=FROZEN/'sources/submission001/lean'":"SOURCE=Path("+repr(str(SRC))+")",
             "PROJECT=Path('deps-project')":"PROJECT=Path("+repr(str(project))+")",
             "TC=Path('lean-runtime')":"TC=Path("+repr(str(tc))+")"}
    for a,b in changes.items():
        require(backend.count(a)==1,'unexpected backend realization')
        backend=backend.replace(a,b)
    bp=out/'review007_backend_bound.py';bp.write_text(backend)
    (out/'BACKEND_BINDING.diff').write_text(''.join(difflib.unified_diff(original.splitlines(True),backend.splitlines(True),fromfile='review007/build_review.py',tofile='bound_backend.py')))
    for mode in ['prepare','build']:
        with (out/(mode+'.stdout.txt')).open('w') as so,(out/(mode+'.stderr.txt')).open('w') as se:
            proc=subprocess.run([sys.executable,'-B',str(bp),mode],stdout=so,stderr=se)
        require(proc.returncode==0,'backend '+mode+' failed; see saved raw logs')
    built=json.loads((out/'BUILD_RESULT.json').read_text())
    require(built['complete'] and built['all_pass'] and len(built['results'])==31,'local build incomplete or failed')
    require(json.loads((out/'LOCAL_IMPORT_DAG.json').read_text())['order']==dag['order'],'local DAG changed')
    settings=json.loads((out/'BUILD_ENV.json').read_text());env=dict(os.environ)
    env['LEAN_PATH']=settings['LEAN_PATH'];env['LEAN_NUM_THREADS']='1'
    spec=importlib.util.spec_from_file_location('bound_review_backend',bp);r=importlib.util.module_from_spec(spec)
    oldargv=sys.argv;sys.argv=[str(bp)]
    try:spec.loader.exec_module(r)
    finally:sys.argv=oldargv
    for n in fixture_names:(out/'src'/f'{n}.lean').write_bytes((REVIEW/'src'/f'{n}.lean').read_bytes())
    checks=[]
    def lean(n):
        return r.command('entry_'+n,[str(tc/'bin/lean'),'-j1','-M4096','-o',str(out/'lib'/f'{n}.olean'),n+'.lean'],out/'src',env)
    types=lean('ReviewerTypes');require(types['returncode']==0,'complete type contracts failed')
    parsed={name:sorted(a.strip() for a in ax.split(',') if a.strip()) for name,ax in re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",types['stdout']+'\n'+types['stderr'])}
    expected=json.loads((REVIEW/'AXIOM_AUDIT.json').read_text())['exact_sets']
    require(parsed==expected and len(parsed)==34,'exact34 axiom sets differ')
    save('AXIOM_SETS.json',parsed)
    semantic=lean('ReviewerSemantics');require(semantic['returncode']==0,'semantic/boundary fixtures failed')
    controls=json.loads((REVIEW/'CONTROL_RESULT.json').read_text())['negatives']
    for c in controls:
        d=lean(c['check']);text=d['stdout']+'\n'+d['stderr']
        resource_problem=d.get('timeout',False) or bool(re.search(r'out of memory|maximum number of heartbeats|maximum recursion|failed to create thread|unknown module|unknown identifier|unexpected token|stack overflow|object file .* does not exist',text,re.I))
        passed=d['returncode']==1 and c['diagnostic'] in text and not resource_problem
        if 'Tactic `decide`' in c['diagnostic']:passed=passed and 'is false' in text
        checks.append({'name':c['check'],'passed':passed,'returncode':d['returncode'],'diagnostic':c['diagnostic'],'resource_or_import_failure':resource_problem})
        save('NEGATIVE_CONTROLS.json',checks)
        require(passed,'intended rejection not established: '+c['check'])
    kernels=[]
    if args.kernel:
        for n in ['Submission.EFamily','Submission.Connections','Submission.SixMixFinite']:
            d=r.command('entry_kernel_'+n,[str(tc/'bin/leanchecker'),'-v',n],out/'src',env)
            require(d['returncode']==0 and 'replaying '+n in d['stdout']+'\n'+d['stderr'],'selected kernel replay failed: '+n)
            kernels.append({'module':n,'passed':True,'mode':'same default kernel replayFromImports'})
    for name,sha in dag['source_hashes'].items():require(H(SRC/(name.replace('.','/')+'.lean'))==sha,'input changed during run')
    result={'status':'PASS_PORTABLE008_REVIEWED_LOCAL_SCOPE','local_modules':31,'complete_new_types':34,'inherited_type_contracts':4,
      'exact_axiom_sets':34,'positive_semantic_examples':20,'intended_negative_controls':checks,'selected_kernel_replays':kernels,
      'source_unchanged':True,'new_independent_review':False,'fresh_external_source_rebuild':False,
      'trust_boundary':'same fixed runtime/kernel and existing pinned external compiled caches',
      'limits':{'Lean_j':1,'Lean_M_MiB':4096,'AS_bytes':16*1024**3,'CPU_soft_hard_seconds':[180,181],'wall_seconds':240},
      'no_install_fetch_update_or_cloud_write':True}
    save('RESULT.json',result);print(json.dumps(result,ensure_ascii=False,indent=2));return 0

if __name__=='__main__':
    try:sys.exit(main())
    except (RuntimeError,OSError,subprocess.SubprocessError,ValueError,KeyError) as exc:
        print(json.dumps({'status':'STOP_OR_FAIL','reason':str(exc),'inconclusive_is_not_a_mathematical_counterexample':True},ensure_ascii=False));sys.exit(2)
