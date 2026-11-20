"""Rebuild every labelled shortest-path edge from the recovered literal vertices."""
from collections import Counter
import json
from pathlib import Path
from sair_text_moves import move, height, encode
from sair_verifier.core import apply_move, INVERSE_MOVE

ROOT = Path(__file__).resolve().parent
def signed(state):
    conv = {'x':1, 'X':-1, 'y':2, 'Y':-2}
    return tuple(tuple(conv[c] for c in word) for word in state)

def checked_move(v,op):
    w=move(v,op)
    assert encode(apply_move(signed(v),op))==w
    assert move(w,INVERSE_MOVE[op])==v
    return w

def replay(c):
    s=tuple(c['start'])
    states=[s]
    for op in c['moves']:
        s=checked_move(s,op)
        states.append(s)
    assert states==list(map(tuple,c['states'])) and s==tuple(c['goal'])
    return max(map(height,states))

def read(name):
    return json.loads((ROOT/name).read_text())

def analyze():
    src=('xyxYXY','xxxYYYY')
    dst=('XyyyxYYYY','xxYYYYYXyyyyy')
    old=read('bridge42.json'); prior=read('bridge41.json')
    assert len(old['moves'])==42 and replay(old)==22
    assert len(prior['moves'])==41 and replay(prior)==25
    assert tuple(old['start'])==tuple(prior['start'])==src and tuple(old['goal'])==tuple(prior['goal'])==dst
    bydepth=[[] for _ in range(42)]
    for line in (ROOT/'vertices28.tsv').read_text().splitlines():
        d,u,v=line.split('\t');bydepth[int(d)].append((u,v))
    assert bydepth[0]==[src] and bydepth[-1]==[dst]
    depth={v:d for d,layer in enumerate(bydepth) for v in layer}
    assert len(depth)==sum(map(len,bydepth))
    keys=sorted(depth,key=lambda v:(depth[v],v))
    edges={v:[(op,w) for op in range(14) if depth.get(w:=checked_move(v,op))==depth[v]+1] for v in keys}
    u,v=map(tuple,old['states'][35:37]); op=old['moves'][35]
    assert (depth[u],depth[v],op)==(34,35,4) and (op,v) in edges[u]
    m=tuple(old['states'][18]); assert m==tuple(prior['states'][17])
    report={}
    for cap in range(24,29):
        ways=Counter({src:1}); tails=Counter({dst:1})
        for x in keys:
            for _,y in edges[x]:
                if height(y)<=cap: ways[y]+=ways[x]
        for x in reversed(keys):
            for _,y in edges[x]:
                if height(x)<=cap:tails[x]+=tails[y]
        paths=ways[dst]; assert paths==tails[src]
        through={x:ways[x]*tails[x] for x in keys if ways[x]*tails[x]}
        live_edges=[(x,c,y) for x in keys for c,y in edges[x] if ways[x] and tails[y] and height(x)<=cap and height(y)<=cap]
        mandatory=[d for d,vs in enumerate(bydepth) if paths and any(through.get(x)==paths for x in vs)]
        mid=[dict(state=x,paths=through[x]) for x in sorted(bydepth[16]) if x in through]
        report[cap]=dict(paths=paths,states=len(through),edges=len(live_edges),midpoints=mid,
                         through_M=through.get(m,0),through_old_edge=ways[u]*tails[v] if (u,op,v) in live_edges else 0,
                         mandatory_state_depths=mandatory)
        if cap==28:assert len(through)==len(keys) and len(live_edges)==sum(map(len,edges.values()))
    for cap in range(25,29):
        report[cap]['exact_peak_paths']=report[cap]['paths']-report[cap-1]['paths']
    return dict(distance=41, caps=report, M=m, original_bottleneck=dict(from_state=u,to_state=v,operation=op),
                left_branch_depth16=16)

if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O')
    print(json.dumps(analyze(),ensure_ascii=False,indent=2))
