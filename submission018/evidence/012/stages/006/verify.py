"""Fast replay of the literal path certificates; no external dependencies."""
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path
from sair_text_moves import height,move,encode
from sair_verifier.core import apply_move,INVERSE_MOVE

ROOT=Path(__file__).resolve().parent
OLD_HASH='9a7c8534637e1f060f55346e41fcf90952faa4fcba68dc5eed6215b813decd52'
EXITS_HASH='3e14b72cb9c8d6448c94d62477df7ce2d940a23a0029b0e59127aabd073d86c4'

def read(name):
    return json.loads((ROOT/name).read_text())

def signed(v):
    signs={'x':1,'X':-1,'y':2,'Y':-2}
    return tuple(tuple(signs[c] for c in w) for w in v)

def replay(v,path):
    states=[v]
    z=signed(v)
    for op in path:
        assert type(op) is int and 0<=op<14
        v=move(v,op);z=apply_move(z,op)
        assert encode(z)==v
        states.append(v)
    return states

def check():
    assert hashlib.sha256((ROOT/'bridge42.json').read_bytes()).hexdigest()==OLD_HASH
    old,new=read('bridge42.json'),read('bridge41.json')
    a,s=map(tuple,(old['start'],old['goal']))
    assert a==('xyxYXY','xxxYYYY') and s==('XyyyxYYYY','xxYYYYYXyyyyy')
    for cert,steps,cap in [(old,42,22),(new,41,25)]:
        assert (tuple(cert['start']),tuple(cert['goal']))==(a,s)
        states=replay(a,cert['moves'])
        assert states==list(map(tuple,cert['states'])) and states[-1]==s
        assert len(cert['moves'])==cert['steps']==steps and max(map(height,states))==cert['peak']==cap
        reverse_path=[INVERSE_MOVE[op] for op in reversed(cert['moves'])]
        assert replay(s,reverse_path)==states[::-1]
    assert old['states'][18:]==new['states'][17:]
    assert old['moves'][18:]==new['moves'][17:] and len(new['moves'][17:])==24
    assert new['heights']==list(map(height,states)) and max(new['heights'][:18])==25
    dag=read('dag.json')
    vertices=list(map(tuple,dag['vertices']));layers=dag['layers']; layers_by_state=dict(zip(vertices,layers))
    assert len(vertices)==len(set(vertices))==154 and vertices[0]==a and vertices[-1]==s
    paths=Counter({a:1});edge_count=0
    arcs=[]
    for i,x in enumerate(vertices):
        for op in range(14):
            y=move(x,op)
            if layers_by_state.get(y)==layers[i]+1:
                paths[y]+=paths[x];arc=(i,op,vertices.index(y))
                arcs.append(arc);edge_count+=1
    assert arcs==list(map(tuple,dag['edges'])) and edge_count==231 and paths[s]==119880
    raw=(ROOT/'step005_new_exits.txt.gz').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==EXITS_HASH
    exits={tuple(line.split()) for line in gzip.decompress(raw).decode().splitlines()}
    assert len(exits)==63788 and exits.isdisjoint(vertices)
    # Verify every saved corridor witness independently of the compiled packed implementation.
    corridors=0
    for path in sorted(ROOT.glob('tube*.jsonl')):
        for row in map(json.loads,path.read_text().splitlines()):
            sequence=replay(a,row['moves'])
            assert sequence[-1]==s and len(row['moves'])==row['distance'] and max(map(height,sequence))<=row['cap']
            corridors+=1
    return dict(result='PASS',cap22_paths=paths[s],dag_states=len(vertices),dag_edges=edge_count,
                literal_005_exit_overlap=0,new_steps=len(new['moves']),new_peak=max(new['heights']),
                rejoin_state=new['states'][17],suffix_steps=24,corridor_certificates_replayed=corridors,
                bidirectional_literal_replay=True)

if __name__=='__main__':
    if not __debug__: raise SystemExit('Run without -O')
    print(json.dumps(check(),indent=2))
