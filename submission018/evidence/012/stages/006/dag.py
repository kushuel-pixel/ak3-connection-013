"""Recover the published 119,880 cap-22 geodesics as a labelled acyclic graph."""
from collections import Counter, deque
import json
from pathlib import Path

from sair_text_moves import height, move

ROOT=Path(__file__).resolve().parent
MIDDLE=[
    ("YYYYXyyyx","YxYXYxyyy"), ("xYYYYXyyy","YYxYXYxyyyy"),
    ("xYYYYXyyy","yXYYxYYYXyyyy"), ("xyyxYYYYXyX","YxyXYYXyy"),
    ("yxYYYYXyy","yxyXYYX"), ("yyxYYYYXy","xyXYYXy"),
]


def distances(start,domain):
    queue=deque([start])
    dist={start:0}
    while queue:
        v=queue.popleft()
        for op in range(14):
            w=move(v,op)
            if w in domain and w not in dist:
                dist[w]=dist[v]+1
                queue.append(w)
    return dist


def build():
    ref=list(map(tuple,json.loads((ROOT/'bridge42.json').read_text())['states']))
    front=set(ref)|set(MIDDLE)
    domain=set(front)
    for r in range(1,7):
        nxt=set()
        for v in front:
            for op in range(14):
                w=move(v,op)
                if height(w)<=22 and w not in domain:
                    nxt.add(w)
        front=nxt
        domain.update(nxt)
        a=distances(ref[0],domain)
        b=distances(ref[-1],domain)
        vertices=sorted((v for v in a if v in b and a[v]+b[v]==42),key=lambda v:(a[v],v))
        ids={v:i for i,v in enumerate(vertices)}
        paths=Counter({ref[0]:1})
        edges=[]
        for i,v in enumerate(vertices):
            for op in range(14):
                w=move(v,op)
                if w in ids and a[w]==a[v]+1:
                    paths[w]+=paths[v]
                    edges.append((i,op,ids[w]))
        count=paths[ref[-1]]
        print(r,len(domain),len(vertices),len(edges),count,flush=True)
        if count==119880:
            assert (len(vertices),len(edges))==(154,231)
            data=dict(radius=r,vertices=vertices,layers=[a[v] for v in vertices],edges=edges,paths=count)
            (ROOT/'dag.json').write_text(json.dumps(data)+'\n')
            (ROOT/'dag.tsv').write_text(''.join(f'{a[v]} {v[0]} {v[1]}\n' for v in vertices))
            return
    raise RuntimeError('The recovered path count differs from the published count')


if __name__=='__main__':
    if not __debug__:raise SystemExit('Run without -O')
    build()
