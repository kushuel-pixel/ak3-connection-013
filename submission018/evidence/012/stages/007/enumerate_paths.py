"""Explicitly visit every label sequence in the supplied shortest-path graphs."""
from collections import Counter
import json
from pathlib import Path
from analyze import ROOT, checked_move, height, read, replay

def expanded():
    ref=read('bridge42.json'); ref_states=list(map(tuple,ref['states']))
    a,s=ref_states[0],ref_states[-1]
    m=ref_states[18]
    bottleneck=ref_states[35],ref['moves'][35],ref_states[36]
    data=read('cap22_dag.json')
    vs=list(map(tuple,data['vertices'])); d=dict(zip(vs,data['layers']))
    inputs=[(d,42)]
    lines=(ROOT/'vertices28.tsv').read_text().splitlines()
    inputs.append(({(u,v):int(i) for i,u,v in (line.split('\t') for line in lines)},41))
    results={}; bypass=None
    for depths,n in inputs:
        arcs={v:[(op,w) for op in range(14) if depths.get(w:=checked_move(v,op))==i+1] for v,i in depths.items()}
        counts=Counter();peak_counts=Counter()
        ops=[];states=[a]
        def visit(v,peak,used_m,used_edge):
            nonlocal bypass
            if v==s:
                assert len(ops)==n
                peak_counts[peak]+=1
                counts['paths']+=1;counts['old_edge']+=used_edge;counts['M']+=used_m
                counts['skip_both']+=not (used_m or used_edge)
                if n==41 and not (used_m or used_edge) and peak==25 and bypass is None:
                    bypass=dict(start=a,goal=s,moves=ops.copy(),states=states.copy(),peak=peak)
                return
            for op,w in arcs[v]:
                ops.append(op);states.append(w)
                visit(w,max(peak,height(w)),used_m or w==m,used_edge or (v,op,w)==bottleneck)
                ops.pop();states.pop()
        visit(a,height(a),False,False)
        results[n]=dict(counts=counts,peak_histogram=peak_counts)
    assert results[42]['counts']['old_edge']==results[42]['counts']['paths']==119880
    assert bypass and replay(bypass)==25 and len(bypass['moves'])==41
    report=read('geodesics.json')['caps']
    assert sum(results[41]['peak_histogram'].values())==report['28']['paths']
    for cap in range(25,29):
        assert results[41]['peak_histogram'][cap]==report[str(cap)]['exact_peak_paths']
    assert results[41]['counts']['M']==report['28']['through_M']
    assert results[41]['counts']['old_edge']==report['28']['through_old_edge']
    return results,bypass

if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O')
    counts,example=expanded()
    print(json.dumps(dict(counts=counts,bypass=example),indent=2))
