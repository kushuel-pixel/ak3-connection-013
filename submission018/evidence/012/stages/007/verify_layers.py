"""Check the entire shortest-path graph against the second word encoding."""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import numpy as np
from analyze import checked_move, height, ROOT

def low_key(s):
    u,v=s
    letters='xyXY'
    z=sum(letters.index(c)<<(2*i) for i,c in enumerate(u+v))
    return (((1<<(2*(len(u)+len(v))))|z)<<5)|len(u)

def bucket(z):
    mask=(1<<64)-1
    z=((z^(z>>30))*0xbf58476d1ce4e5b9)&mask
    z=((z^(z>>27))*0x94d049bb133111eb)&mask
    return (z^(z>>31))>>58

def verify(left,right):
    graph=defaultdict(set)
    for ln in (ROOT/'vertices28.tsv').read_text().splitlines():
        d,u,v=ln.split('\t');graph[int(d)].add((u,v))
    mid=json.loads((ROOT/'alternate_mid28.json').read_text())
    assert mid['hits']==len(graph[16]) and set(mid['keys'])==set(map(low_key,graph[16]))
    for root,steps,layer in [(left,16,lambda i:i),(right,25,lambda i:41-i)]:
        for d in range(steps,0,-1):
            candidate=defaultdict(set)
            for v in graph[layer(d)]:
                for op in range(14):
                    w=checked_move(v,op)
                    if height(w)<=28:
                        k=low_key(w);candidate[bucket(k)].add(k)
            matches=set()
            for b,keys in candidate.items():
                values=np.fromfile(root/f'{d-1}_{b}.bin',dtype=np.uint64)
                for k in keys:
                    if np.any(values==np.uint64(k)):matches.add(k)
            expected=set(map(low_key,graph[layer(d-1)]))
            assert matches==expected,(root,d,matches^expected)
    return dict(result='PASS',midpoint_count=len(graph[16]),checked_predecessor_layers=41,
                checked_states=sum(map(len,graph.values())))

if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O')
    p=argparse.ArgumentParser();p.add_argument('left',type=Path);p.add_argument('right',type=Path);a=p.parse_args()
    print(json.dumps(verify(a.left,a.right)))
