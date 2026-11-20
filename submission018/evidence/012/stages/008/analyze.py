"""Verify and count the literal shortest paths recovered from the full cap-29 balls."""
from collections import Counter
from pathlib import Path
import json
from sair_text_moves import encode, height, move
from sair_verifier.core import apply_move, INVERSE_MOVE
ROOT=Path(__file__).resolve().parent
SIGNS={'x':1,'X':-1,'y':2,'Y':-2}
A=('xyxYXY','xxxYYYY')
S=('XyyyxYYYY','xxYYYYYXyyyyy')

def step(v,op):
    w=move(v,op)
    z=tuple(tuple(SIGNS[c] for c in s) for s in v)
    assert encode(apply_move(z,op))==w and move(w,INVERSE_MOVE[op])==v
    return w

def graph(path):
    out={}
    for ln in path.read_text().splitlines():
        d,u,v=ln.split('\t')
        assert (u,v) not in out
        out[u,v]=int(d)
    return out

def read(name):
    return json.loads((ROOT/name).read_text())

def replay(states,ops):
    assert states[0]==A and states[-1]==S and len(states)==len(ops)+1
    assert all(step(a,op)==b for a,op,b in zip(states,ops,states[1:]))
    assert all(step(b,INVERSE_MOVE[op])==a for a,op,b in zip(states,ops,states[1:]))

def analyze():
    cert=read('bridge41.json');old=list(map(tuple,cert['states']))
    assert len(cert['moves'])==41 and max(map(height,old))==25
    replay(old,cert['moves'])
    g=graph(ROOT/'vertices29.tsv')
    seeds=graph(ROOT/'vertices28.tsv')
    assert g[A]==0 and max(g.values())==g[S]
    length=g[S]
    edges={v:[(op,w) for op in range(14) if g.get(w:=step(v,op))==g[v]+1] for v in g}
    order=sorted(g,key=lambda v:(g[v],v))
    def counts(cap):
        prefix=Counter({A:1});suffix=Counter({S:1})
        for v in order:
            for op,w in edges[v]:
                if height(w)<=cap:prefix[w]+=prefix[v]
        for v in reversed(order):
            if height(v)<=cap:
                for op,w in edges[v]:suffix[v]+=suffix[w]
        assert prefix[S]==suffix[A]
        return prefix,suffix
    all_a,all_s=counts(29);n=all_a[S]
    assert n and all(all_a[v]*all_s[v]>0 and height(v)<=29 for v in g)
    low_a,low_s=counts(28);nlow=low_a[S];assert nlow==(71412 if length==41 else 0)
    if length==41:assert {v for v in g if low_a[v]*low_s[v]}==set(seeds)
    points=sorted(v for v in g if g[v]==16)
    forced=[(g[v],v) for v in order if all_a[v]*all_s[v]==n]
    def membership(x):
        return all_a[x]*all_s[x]
    # Pick a shortest path with an actual visit to length 29 whenever possible.
    hit=next((v for v in order if height(v)==29),S)
    x=hit;prefix=[]
    while x!=A:
        op,v=next((op,v) for v in order for op,w in edges[v] if w==x)
        prefix.append((op,x));x=v
    suffix=[];x=hit
    while x!=S:
        op,w=edges[x][0];suffix.append((op,w));x=w
    path=list(reversed(prefix))+suffix
    states=[A]+[v for _,v in path];ops=[op for op,_ in path];replay(states,ops)
    peak=max(map(height,states));assert peak<=29 and (not n-nlow or peak==29)
    old_u=('xYYYYXyyy','yyxxYX');old_v=('xYYYYXyyy','yyxxYYYYYXyyy')
    old_cross=all_a[old_u]*all_s[old_v] if (4,old_v) in edges.get(old_u,[]) else 0
    return dict(distance=length,through_old_bottleneck=old_cross,states=len(g),edges=sum(map(len,edges.values())),paths=n,
                paths_at_most_peak28=nlow,paths_exact_peak29=n-nlow,
                states_at_length29=sum(height(v)==29 for v in g),
                midpoint_paths=[dict(state=v,paths=membership(v)) for v in points],
                forced=[dict(depth=d,state=v) for d,v in forced],
                witness=dict(peak=peak,steps=len(ops),moves=ops,states=states))

if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O')
    print(json.dumps(analyze(),indent=2))
