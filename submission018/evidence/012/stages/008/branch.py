"""Reconstruct both five-move arms and check the identity on formal free letters."""
from collections import Counter
import json
from analyze import ROOT,graph,step,height,read
from sair_text_moves import reduce,move
OLD=(5,11,3,7,4)
NEW=(3,7,4,11,2)
def walk(p,ops,action):
    path=[p]
    for op in ops:path.append(action(path[-1],op))
    return path
def inspect():
    g=graph(ROOT/'vertices29.tsv');base=graph(ROOT/'vertices28.tsv')
    a=('xYXYxy','xxxYYYY')
    arms=[walk(a,ops,step) for ops in (OLD,NEW)]
    old,new=arms;q=old[-1]
    assert q==new[-1] and g[a]==2 and g[q]==7
    assert set(old)&set(new)=={a,q} and len(set(old+new))==10
    assert {v for v in g if v not in base}==set(new[1:-1])
    assert [height(v) for v in old]==[13,19,17,24,22,27]
    assert [height(v) for v in new]==[13,20,18,29,27,27]
    arcs={v:[(op,w) for op in range(14) if g.get(w:=step(v,op))==g[v]+1] for v in g}
    prefix=Counter({next(v for v in g if g[v]==0):1})
    suffix=Counter({next(v for v in g if g[v]==41):1})
    for v in sorted(g,key=g.get):
        for op,w in arcs[v]:prefix[w]+=prefix[v]
    for v in sorted(g,key=g.get,reverse=True):
        for op,w in arcs[v]:suffix[v]+=suffix[w]
    assert prefix[a]==1 and prefix[q]==2 and suffix[q]==34624
    assert all(len(arcs[v])==1 for v in new[1:-1])
    assert read('geodesics29.json')['paths_exact_peak29']==suffix[q]
    # Evaluate words on free generators a,b,x, obtaining an identity under every substitution.
    C=lambda w:reduce('X'+w+'x')
    t=C('aB')
    formula=(C('a'+t),C('b'+t))
    assert walk(('a','b'),OLD,move)[-1]==walk(('a','b'),NEW,move)[-1]==formula
    return dict(old_operations=OLD,new_operations=NEW,old_states=old,new_states=new,
                old_heights=list(map(height,old)),new_heights=list(map(height,new)),suffix_choices=suffix[q],
                common_symbolic_endpoint=formula,loop_length=10)
if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O')
    print(json.dumps(inspect(),indent=2))
