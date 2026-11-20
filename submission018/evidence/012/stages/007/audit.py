"""Lightweight check of the saved native logs, graph and literal witnesses."""
import json
from analyze import ROOT, analyze, read
from enumerate_paths import expanded

def rows(name):
    return [json.loads(line) for line in (ROOT/name).read_text().splitlines()]

def verify():
    def ball(name,side):
        out=rows(name);sizes=[];total=0
        for d,row in enumerate(out):
            total+=row['sphere']
            assert row==dict(cap=28,side=side,depth=d,sphere=row['sphere'],ball=total)
            sizes.append(total)
        assert sizes[0]==1
        return sizes
    left,right=ball('A28.jsonl',0),ball('S28_r25.jsonl',1)
    assert left==ball('checkA28_r16.jsonl',0) and right==ball('checkS28.jsonl',1)
    assert left[:16]==ball('checkA28.jsonl',0) and right[:25]==ball('S28.jsonl',1)
    hashes=[tuple(map(int,ln.split())) for ln in (ROOT/'meet28.tsv').read_text().splitlines()]
    assert len({z for _,_,z in hashes})==len(hashes)==2
    assert all((x,y)==(16,25) for x,y,_ in hashes)
    assert read('alternate28.json')==dict(radii=[15,25],sizes=[left[15],right[25]],hits=0,keys=[])
    alt=read('alternate_mid28.json')
    assert alt['radii']==[16,25] and alt['sizes']==[left[16],right[25]] and alt['hits']==len(set(alt['keys']))==2
    assert read('alternate_dag.json')==dict(result='PASS',midpoint_count=2,checked_predecessor_layers=41,checked_states=155)
    g=rows('global26.jsonl')
    assert all(r['hits']==0 and r['cap']==26 for r in g)
    assert g[-1]['radii']==[16,24] and g[-1]['sizes']==[115350044,101426183]
    assert json.loads(json.dumps(analyze()))==read('geodesics.json')
    counts,bypass=expanded()
    assert json.loads(json.dumps(dict(counts=counts,bypass=bypass)))==read('explicit_check.json')
    print('PASS: native logs agree, 155 shortest-path states, 71,412 literal move sequences, bottleneck bypass replayed.')

if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O')
    verify()
