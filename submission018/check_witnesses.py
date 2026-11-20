"""Verify the four paths in the revised note against the archived move semantics."""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
STAGES = HERE / "evidence/012/stages"
if not STAGES.is_dir():
    STAGES = HERE.parent / "stages"
sys.path.insert(0, str(STAGES / "010"))
from verify import A, S, U, V, height, run


def search_witness(cap):
    path = STAGES / f"010/search{cap}.jsonl"
    return json.loads(path.read_text(encoding="utf-8").splitlines()[-1])["moves"]


def main():
    if not __debug__:
        raise SystemExit("Run without Python optimization.")
    form = (HERE / "FORM_DESCRIPTION.txt").read_text(encoding="utf-8")
    rows = [p.split() for p in form.split("\n\n") if p.split() and all(w.isdecimal() for w in p.split())]
    printed, = rows
    bypass = [int(w) for w in printed]
    assert bypass == json.loads((STAGES / "010/bypasses.json").read_text(encoding="utf-8"))["25"]
    through = json.loads((STAGES / "006/bridge41.json").read_text(encoding="utf-8"))["moves"]
    tests = [
        ("bypass22", search_witness(22), 44, 22, list(range(37, 45)), [], [], [38]),
        ("bypass23", search_witness(23), 42, 23, [11, 12, 13, 14], [], [], []),
        ("bypass25", bypass, 41, 25, [9], [], [], []),
        ("through25", through, 41, 25, [10, 11], [(35, 4, U, V)], [34], [35]),
    ]
    for label, moves, length, peak, peak_steps, crossings, u_steps, v_steps in tests:
        path = run(A, moves)
        heights = list(map(height, path))
        assert len(moves) == length and path[-1] == S
        assert max(heights) == peak and [i for i, h in enumerate(heights) if h == peak] == peak_steps
        assert [i for i, p in enumerate(path) if p == U] == u_steps
        assert [i for i, p in enumerate(path) if p == V] == v_steps
        crossed = [(i, m, a, b) for i, (m, a, b) in enumerate(zip(moves, path, path[1:]), 1)
                   if (a, b) in ((U, V), (V, U))]
        assert crossed == crossings
        print(f"{label}: {length} moves, peak {peak} at {peak_steps}, edge traversals {len(crossed)}")
    print("PASS revised form, endpoints, peaks, state visits and edge traversals")


if __name__ == "__main__":
    main()
