"""Check the joined cap-30 result, input counts and a literal upper bound."""
from pathlib import Path
import json
from sair_text_moves import height,move
ROOT=Path(__file__).resolve().parent
def read(n):return json.loads((ROOT/n).read_text())
def rows(n):return [json.loads(l) for l in (ROOT/n).read_text().splitlines()]
def run():
    a,s=rows('A30.jsonl'),rows('S30.jsonl')
    for group,side,r in [(a,0,15),(s,1,24)]:
        t=0;assert len(group)==r+1
        for i,rec in enumerate(group):
            t+=rec['sphere']
            assert rec==dict(cap=30,side=side,depth=i,sphere=rec['sphere'],ball=t)
    assert rows('A30_pilot.jsonl')==rows('A30_second_pilot.jsonl')==a[:9]
    assert rows('S30_pilot.jsonl')==rows('S30_second_pilot.jsonl')==s[:16]
    assert read('compareA30.json')==dict(result='PASS',depth=8,exact_state_keys=a[8]['ball'])
    assert read('compareS30.json')==dict(result='PASS',depth=15,exact_state_keys=s[15]['ball'])
    for name,data in [('A',a),('S',s)]:
        receipt=read('shards'+name+'30.json')
        assert receipt['identity'].startswith('packed-block9-v1 30 ') and len(receipt['layers'])==len(data)
        for rec,shards in zip(data,receipt['layers']):
            assert rec['depth']==shards['depth'] and rec['sphere']==shards['total']==sum(n for n,h in shards['shards'])
            assert len(shards['shards'])==64 and all(len(bytes.fromhex(h))==32 for n,h in shards['shards'])
    assert read('codec.json')['label_checks']==605430 and read('codec.json')['result']=='PASS'
    assert read('test_stream.json')==read('test_stream_low.json')
    ref=read('bridge41.json');state=tuple(ref['start']);trace=[state]
    for op in ref['moves']:state=move(state,op);trace.append(state)
    assert len(ref['moves'])==41 and list(map(tuple,ref['states']))==trace
    assert max(map(height,trace))==25 and trace[0]==('xyxYXY','xxxYYYY') and trace[-1]==('XyyyxYYYY','xxYYYYYXyyyyy')
    minimums=[]
    for n,x,y,p,q in [('forward30.json',a,s,15,24),('reverse30.json',s,a,24,15)]:
        log=read(n)
        assert log['cap']==30 and log['radii']==[p+1,q]
        assert log['left_stored_radius']==p and log['left_stored_ball']==x[-1]['ball'] and log['right_ball']==y[-1]['ball']
        assert 0<log['outer_label_visits'] and 0<=log['candidate_visits']<=log['left_stored_ball']+log['outer_label_visits']
        assert len(log['matches'])==len({key for key,d in log['matches']})
        tsv='forward_depths.tsv' if n.startswith('forward') else 'reverse_depths.tsv'
        depths=[tuple(map(int,ln.split())) for ln in (ROOT/tsv).read_text().splitlines()]
        assert sorted((k,b) for a0,b,k in depths)==sorted(map(tuple,log['matches']))
        minimums.append(min((a0+b for a0,b,k in depths),default=41))
    assert minimums[0]==minimums[1]
    if minimums[0]<41:
        shorter=read('shorter.json');states=list(map(tuple,shorter['states']))
        assert states[0]==trace[0] and states[-1]==trace[-1] and max(map(height,states))==shorter['peak']==30
        assert len(shorter['moves'])==len(states)-1==shorter['steps']==minimums[0]
        assert all(move(u,op)==v for u,op,v in zip(states,shorter['moves'],states[1:]))
    print(json.dumps(dict(result='PASS',distance=minimums[0],forward_matches=len(read('forward30.json')['matches']),reverse_matches=len(read('reverse30.json')['matches']))))
if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O')
    run()
