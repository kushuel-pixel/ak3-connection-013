"""Read the exact distances of the few surviving streamed midpoints."""
from pathlib import Path
import json,sys
import numpy as np
def bucket(value):
    mask=(1<<64)-1
    value=((value^(value>>30))*0xbf58476d1ce4e5b9)&mask
    value=((value^(value>>27))*0x94d049bb133111eb)&mask
    return (value^(value>>31))>>58
def distances(src,cap_depth,stream):
    matches=stream['matches']
    assert len(matches)==len({key for key,_ in matches})
    for key,rhs in matches:
        b=bucket(key);left=cap_depth+1
        for d in range(cap_depth+1):
            words=np.fromfile(src/f'{d}_{b}.bin',dtype=np.uint64)
            if np.any(words==np.uint64(key)):left=d;break
        yield left,rhs,key
if __name__=='__main__':
    root,path,depth,output=sys.argv[1:]
    records=list(distances(Path(root),int(depth),json.loads(Path(path).read_text())))
    Path(output).write_text(''.join(f'{a}\t{b}\t{k}\n' for a,b,k in records))
