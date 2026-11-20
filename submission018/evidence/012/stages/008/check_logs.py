"""Check layer receipts, midpoint signs, local counts and the positive path."""
import json
from analyze import ROOT, analyze, read

def rows(name):
    return [json.loads(line) for line in (ROOT/name).read_text().splitlines()]

def ball(side,tag,radius):
    main=rows(f'{tag}29.jsonl')
    assert main==rows(f'check{tag}29.jsonl')
    receipt=read(f'shards{tag}29.json')
    assert receipt['identity'].startswith('packed-v1 29 ')
    assert len(main)==len(receipt['layers'])==radius+1
    total=0
    for d,(r,sectors) in enumerate(zip(main,receipt['layers'])):
        n=sectors['total'];total+=n
        assert r==dict(cap=29,side=side,depth=d,sphere=n,ball=total)
        assert sectors['depth']==d and len(sectors['shards'])==64 and sum(k for k,_ in sectors['shards'])==n
        assert all(len(bytes.fromhex(h))==32 for _,h in sectors['shards'])
    return [r['ball'] for r in main]

def key(p):
    u,v=p;w=1
    for c in u+v:w=w*4+'xXyY'.index(c)
    return (w<<5)|len(v)

def check():
    left=ball(0,'A',16);right=ball(1,'S',25)
    full=[tuple(map(int,ln.split())) for ln in (ROOT/'meet29.tsv').read_text().splitlines()]
    limited=[tuple(map(int,ln.split())) for ln in (ROOT/'meet29_40.tsv').read_text().splitlines()]
    assert [r for r in full if r[1]<=24]==limited==[]
    alt=read('alternate40.json')
    assert alt==dict(radii=[15,25],sizes=[left[15],right[25]],hits=0,keys=[])
    assert min(x+y for x,y,_ in full)==41 and all((x,y)==(16,25) for x,y,_ in full)
    report=analyze()
    assert json.loads(json.dumps(report))==read('geodesics29.json')
    assert {key(r['state']) for r in report['midpoint_paths']}=={k for _,_,k in full}
    assert report['paths']==sum(r['paths'] for r in report['midpoint_paths'])
    for l,r in [(4,5),(4,6)]:
        log=rows(f'local_{l}_{r}.jsonl')
        assert log[-1]['seeds']==155 and log[-1]['left_radius']==l and log[-1]['right_radius']==r
        assert log[-1]['left_unique']<=log[-1]['left_visits'] and log[-1]['right_visits']>log[-1]['left_visits']
    from branch import inspect
    assert json.loads(json.dumps(inspect()))==read('branch29.json')
    assert rows('local_4_6.jsonl')[-1]['improving_matches']==0
    print('PASS: cap-29 complete layer audits, two split checks, shortest graph and literal witness.')
if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O')
    check()
