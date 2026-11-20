"""Replay the exit and the two renamed paths using the archived SAIR verifier."""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent
STAGES = HERE / "evidence/012/stages"
if not STAGES.is_dir():
    STAGES = HERE.parent / "stages"
sys.path.insert(0, str(STAGES / "010"))
from verify import A, S, U, V, height, run

TAU = str.maketrans("xXyY", "YyXx")
PERM = (0, 1, 2, 3, 4, 5, 9, 8, 7, 6, 13, 12, 11, 10)
E3 = ("XyyyxYYYY", "xxYYYYXyyyy")
EXIT = [6] + [9]*4 + [5] + [13]*4 + [2] + [12]*4 + [3, 4, 2, 5, 2, 8]


def tau(state):
    return tuple(word.translate(TAU) for word in state)


def inspect_path(start, moves, end, edge):
    path = run(start, moves)
    assert path[-1] == end
    heights = [height(state) for state in path]
    peak = max(heights)
    crossings = []
    for i, (a, b) in enumerate(zip(path, path[1:])):
        if (a, b) in (edge, edge[::-1]):
            crossings.append((i+1, moves[i], "forward" if (a,b) == edge else "backward"))
    return path, dict(moves=len(moves), states=len(path), peak=peak,
                      peak_steps=[i for i, h in enumerate(heights) if h == peak], crossings=crossings)


def main():
    if not __debug__:
        raise SystemExit("Run without Python optimization.")
    twin = ("YXYxyx", "YYYxxxx")
    target = ("yXXXYxxxx", "YYxxxxxyXXXXX")
    assert tau(A) == twin and tau(S) == target
    assert all(PERM[PERM[m]] == m for m in range(14))
    assert tuple(w[3:]+w[:3] for w in twin) == ("xyxYXY", "xxxxYYY")

    rotation = run(("YXYxyx", "YYYYxxx"), [6, 8, 6, 10, 10, 10])
    assert rotation[-1] == A and max(map(height, rotation)) == 13
    exit_path = run(E3, EXIT)
    assert exit_path[-1] == ("x", "y") and len(EXIT) == 21 and max(map(height, exit_path)) == 22
    bridge = json.loads((STAGES / "010/bridge42.json").read_text(encoding="utf-8"))["moves"]
    _, info = inspect_path(A, bridge, S, (U,V))
    assert (info["moves"], info["peak"], info["crossings"]) == (42, 22, [(36, 4, "forward")])
    print("ac-00399 to A: 6 moves, peak 13; A to S: 42 moves, peak 22; E3 to (x,y): 21 moves, peak 22")
    bypass = json.loads((STAGES / "010/bypasses.json").read_text(encoding="utf-8"))["25"]
    through = json.loads((STAGES / "006/bridge41.json").read_text(encoding="utf-8"))["moves"]
    for name, moves, steps, crossed in [("bypass25", bypass, [9], []),
                                        ("through25", through, [10, 11], [(35,4,"forward")])]:
        path = run(A, moves)
        transformed = [PERM[m] for m in moves]
        image, info = inspect_path(twin, transformed, target, (tau(U), tau(V)))
        assert image == [tau(state) for state in path]
        assert all(tau(tau(state)) == state for state in path)
        assert (info["states"], info["peak"], info["peak_steps"], info["crossings"]) == (42,25,steps,crossed)
        print(name, json.dumps(dict(start=twin, finish=target, ids=transformed, **info)))
    print("PASS")


if __name__ == "__main__":
    main()
