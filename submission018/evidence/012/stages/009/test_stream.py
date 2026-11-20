"""Run small negative and positive cases, including an outer-layer-only match."""
from pathlib import Path
import subprocess,json,sys,tempfile
layers,exact,stream=map(lambda s:str(Path(s).resolve()),sys.argv[1:4])
def run(*args):
    return subprocess.check_output(list(map(str,args)),text=True)
def check(t,e,p,q):
    path=t/'endpoints.tsv';path.write_text(e)
    run(layers,path,30,0,p+1,t/'a',1000000,2);run(layers,path,30,1,q,t/'s',1000000,2)
    out=t/'exact.tsv';run(exact,t/'a',t/'s',p+1,q,2,out)
    expected=[tuple(map(int,x.split())) for x in out.read_text().splitlines()]
    streamed=json.loads(run(stream,30,t/'a',t/'s',p,q,t/'tmp',2))
    assert sorted((k,r) for l,r,k in expected)==sorted(map(tuple,streamed['matches']))
    return dict(hits=len(expected),min_length=min((l+r for l,r,k in expected),default=None),
                outer_only=bool(expected) and all(l==p+1 for l,r,k in expected),candidate_visits=streamed['candidate_visits'])
specs=[('xyxYXY xxxYYYY\nXyyyxYYYY xxYYYYYXyyyyy\n',2,4),
       ('xyxYXY xxxYYYY\nxYXYxy xxxYYYY\n',0,1),
       ('xyxYXY xxxYYYY\nxyxYXY xxxYYYY\n',1,1)]
results=[]
for pair,p,q in specs:
    with tempfile.TemporaryDirectory() as tmp:results.append(check(Path(tmp),pair,p,q))
assert results[0]['hits']==0 and results[0]['candidate_visits']>0 and results[1]['min_length']==2 and results[1]['outer_only'] and results[2]['min_length']==0
print(json.dumps(results))
