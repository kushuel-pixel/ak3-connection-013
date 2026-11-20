"""Write file counts and SHA-256 values for one complete family of distance layers."""
import hashlib,json,sys
from pathlib import Path
root=Path(sys.argv[1])
radius=int(sys.argv[2])
rows=[]
for d in range(radius+1):
    got=0;shards=[]
    for b in range(64):
        p=root/f'{d}_{b}.bin'
        size=p.stat().st_size
        assert size%8==0
        with p.open('rb') as f:
            digest=hashlib.file_digest(f,'sha256').hexdigest()
        got+=size//8;shards.append([size//8,digest])
    assert got==int((root/f'{d}.done').read_text())
    rows.append(dict(depth=d,total=got,shards=shards))
print(json.dumps(dict(identity=(root/'identity.txt').read_text().strip(),layers=rows),separators=(',',':')))
