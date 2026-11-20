"""Compare the complete sorted state sets of two searches at every pilot depth."""
import json,sys
from pathlib import Path
import numpy as np
def same(a,b,d):
    count=0
    for i in range(d+1):
        for k in range(64):
            x=np.fromfile(a/f'{i}_{k}.bin',dtype=np.uint64)
            y=np.fromfile(b/f'{i}_{k}.bin',dtype=np.uint64)
            assert len(x)==len(y)
            x.sort();y.sort()
            assert np.array_equal(x,y)
            count+=len(x)
    return count
if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O')
    d=int(sys.argv[3])
    print(json.dumps(dict(result='PASS',depth=d,exact_state_keys=same(Path(sys.argv[1]),Path(sys.argv[2]),d))))
