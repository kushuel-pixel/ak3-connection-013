"""Count fixed-length walks on the 159 recorded states without using their depth labels."""
from collections import Counter
from pathlib import Path
import sys

STAGE = Path(__file__).resolve().parents[1] / "submission018/evidence/012/stages/008"
sys.path.insert(0, str(STAGE))
from sair_verifier.core import apply_move


def pair(first, second):
    letter = {"x": 1, "X": -1, "y": 2, "Y": -2}
    return tuple(tuple(letter[c] for c in word) for word in (first, second))


def walk_counts(edges, start, steps):
    counts = Counter({start: 1})
    for _ in range(steps):
        following = Counter()
        for state, ways in counts.items():
            for neighbor in edges[state]:
                following[neighbor] += ways
        counts = following
    return counts


def main():
    vertices = set()
    for row in (STAGE / "vertices29.tsv").read_text(encoding="utf-8").splitlines():
        _, first, second = row.split("\t")
        vertices.add(pair(first, second))
    assert len(vertices) == 159
    start = pair("xyxYXY", "xxxYYYY")
    finish = pair("XyyyxYYYY", "xxYYYYYXyyyyy")
    join = pair("YXYYxyyyyyX", "xxYYYYYXYxyyyyyX")
    heights = {s: sum(map(len, s)) for s in vertices}
    high_prefix = (7, 9, 3, 7, 4, 11, 2)
    arm_states = [start]
    for move_id in high_prefix:
        arm_states.append(apply_move(arm_states[-1], move_id))
    assert arm_states[-1] == join and set(arm_states) <= vertices
    assert {s for s in vertices if heights[s] >= 29} == {arm_states[5]}
    assert heights[arm_states[5]] == 29

    # Keep one edge per move ID, including any parallel edges and loops.
    neighbors = {s: [apply_move(s, m) for m in range(14)] for s in vertices}
    for cap, expected in [(27, 71412), (28, 71412), (29, 106036)]:
        allowed = {s for s in vertices if heights[s] <= cap}
        forward = {s: [] for s in allowed}
        backward = {s: [] for s in allowed}
        for s in allowed:
            for t in neighbors[s]:
                if t in allowed:
                    forward[s].append(t)
                    backward[t].append(s)
        assert walk_counts(forward, start, 41)[finish] == expected
        assert walk_counts(backward, finish, 41)[start] == expected
        assert walk_counts(forward, join, 34)[finish] == 34624
        assert walk_counts(backward, finish, 34)[join] == 34624
        print(f"159-state graph, cap {cap}: {expected} walks of 41 moves; 34624 suffixes of 34 moves")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without Python optimization.")
    main()
