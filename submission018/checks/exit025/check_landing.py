"""Replay the 39-move example and exhaust its landing component at cap 28."""
from collections import deque
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "evidence/012/stages/010"))
from verify import S, height, run
from sair_verifier.core import apply_move


def integer_pair(words):
    letters = {"x": 1, "X": -1, "y": 2, "Y": -2}
    return tuple(tuple(letters[c] for c in word) for word in words)


def main():
    if not __debug__:
        raise SystemExit("Run without Python optimization.")
    data = json.loads((HERE / "landing39.json").read_text(encoding="utf-8"))
    supplement = (HERE.parents[1] / "EXIT_AND_RENAMING.md").read_text(encoding="utf-8")
    printed = supplement.split("```text\n", 1)[1].split("\n```", 1)[0]
    assert [int(move) for move in printed.split()] == data["moves"]
    path = run(S, data["moves"])
    lengths = list(map(height, path))
    assert len(path) == 40 and len(set(path)) == 40 and path[-1] == tuple(data["end"])
    assert lengths == data["heights"] and lengths[-1] == 28
    assert max(lengths) == 29 and [i for i, h in enumerate(lengths) if h == 29] == list(range(33, 39))

    landing = integer_pair(path[-1])
    seen = {landing}
    queue = deque([landing])
    while queue:
        state = queue.popleft()
        for move in range(14):
            other = apply_move(state, move)
            if sum(map(len, other)) <= 28 and other not in seen:
                seen.add(other)
                assert len(seen) <= 748
                queue.append(other)
    assert len(seen) == 748 and integer_pair(S) not in seen
    print("PASS 39 moves from S, peak 29, the cap-28 landing component has 748 states and excludes S")


if __name__ == "__main__":
    main()
