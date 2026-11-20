"""Replay original and avoiding witnesses as literal ordered word pairs in both directions."""
from pathlib import Path
import json
from sair_text_moves import move, height, encode
from sair_verifier.core import apply_move, INVERSE_MOVE

ROOT = Path(__file__).resolve().parent
A = ('xyxYXY','xxxYYYY')
S = ('XyyyxYYYY','xxYYYYYXyyyyy')
U = ('xYYYYXyyy','yyxxYX')
V = ('xYYYYXyyy','yyxxYYYYYXyyy')

def data(name):
    return json.loads((ROOT/name).read_text())

def run(start, moves):
    path = [start]
    letters = {'x':1,'X':-1,'y':2,'Y':-2}
    integer_state = tuple(tuple(letters[c] for c in w) for w in start)
    for op in moves:
        assert 0 <= op < 14
        integer_state = apply_move(integer_state, op)
        path.append(move(path[-1],op))
        assert encode(integer_state) == path[-1]
    return path

def verify():
    ref = data('bridge42.json')
    old = run(A, ref['moves'])
    assert (old[35], old[36], ref['moves'][35]) == (U,V,4)
    assert old[-1] == S and len(old) == 43 and max(map(height, old)) == 22
    moves = data('bypasses.json')
    for cap in (22,23):
        rows = [json.loads(s) for s in (ROOT/f'search{cap}.jsonl').read_text().splitlines()]
        assert all(r['hits'] == 0 for r in rows[:-1])
        last = rows[-1]
        assert last['hits'] and sum(last['radii']) == len(last['moves'])
        negative = data(f'alternate{cap}.json')
        assert sum(negative['radii']) == len(last['moves'])-1 and negative['hits'] == 0
        moves[str(cap)] = last['moves']
    result = {}
    for key, ops in sorted(moves.items()):
        cap = int(key)
        path = run(A, ops)
        assert path[-1] == S and max(map(height,path)) <= cap
        assert all((p,q) not in ((U,V),(V,U)) for p,q in zip(path,path[1:]))
        assert run(S, [INVERSE_MOVE[op] for op in ops[::-1]]) == path[::-1]
        result[key] = dict(steps=len(ops), peak=max(map(height,path)))
    assert result['24']==dict(steps=42,peak=24)
    assert result['25']==dict(steps=41,peak=25)
    return result

if __name__ == '__main__':
    if not __debug__: raise SystemExit('Run without -O')
    print(json.dumps(verify(),indent=2))
