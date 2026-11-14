#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1]
d=json.loads((root/'FILE_SHA256.json').read_text())
files={str(p.relative_to(root)):p for p in root.rglob('*') if p.is_file() and p.name!='FILE_SHA256.json'}
assert set(files)==set(d['files']), 'file set mismatch'
for name,p in files.items():
    e=d['files'][name]
    assert p.stat().st_size==e['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256'],name
print('PASS: %d files match the self-excluding manifest'%len(files))
