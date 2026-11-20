"""Check recorded ball depths, nonintersection counts and positive witnesses."""
from pathlib import Path
import json
from verify import check,replay,read

ROOT=Path(__file__).resolve().parent


def rows(stem):
    path=ROOT/(stem+'.jsonl')
    out=[json.loads(line) for line in path.read_text().splitlines()]
    if not out: raise ValueError('empty record: '+stem)
    return out


def audit():
    report=check()
    for cap,target in [(23,41),(24,41),(25,40)]:
        run=rows(f'global{cap}')
        prev=[0,0]
        sizes=[1,1]
        for rec in run:
            assert rec['cap']==cap and rec['hits']==0
            diff=[x-y for x,y in zip(rec['radii'],prev)]
            assert diff in ([0,1],[1,0])
            assert all(x>=y for x,y in zip(rec['sizes'],sizes))
            assert rec['sizes'][diff.index(0)]==sizes[diff.index(0)]
            prev,sizes=rec['radii'],rec['sizes']
        assert sum(prev)==target
    for cap,total in [(22,41),(24,41),(25,40)]:
        rec,=rows(f'alternate{cap}')
        assert (rec['cap'],sum(rec['radii']),rec['hits'])==(cap,total,0)
    assert rows('alternate22')[0]['sizes']==[4703381,5300461]
    records=rows('prefix_balls')
    assert [r['cap'] for r in records]==list(range(22,29))
    for rec in records:
        h=rec['hits_by_distance_sum']
        assert rec['radii']==[8,9] and len(h)==18 and sum(h[:17])==0
        assert (h[17]>0)==(rec['cap']>=25)
    for rec in rows('alternate_prefix'):
        if rec['radii']==[8,9]:
            target=records[rec['cap']-22]
            assert rec['sizes']==target['sizes'] and rec['hits']==sum(target['hits_by_distance_sum'])
        else:
            assert (rec['cap'],rec['radii'],rec['hits'])==(28,[8,8],0)
    states=read('bridge41.json')['states']
    assert states[-1]==['XyyyxYYYY','xxYYYYYXyyyyy']
    report.update(full_distance_caps_22_23_24=42,full_distance_cap25=41,
                  first_cap_permitting_41_or_less=25,global_optimality_at_cap28='open',
                  prefix_distance_caps_22_to_24=18,prefix_distance_caps_25_to_28=17)
    return report

if __name__=='__main__':
    if not __debug__:raise SystemExit('Run without -O')
    print(json.dumps(audit(),indent=2))
