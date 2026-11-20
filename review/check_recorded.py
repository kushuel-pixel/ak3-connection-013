"""Enumerate paths only in the fixed layers shipped with submission 018."""
import argparse
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("submission", type=Path, help="root of the extracted 018 ZIP")
    stage = parser.parse_args().submission.resolve() / "evidence/012/stages/008"
    sys.path.insert(0, str(stage))
    from analyze import A, S, graph, height, step

    g = graph(stage / "vertices29.tsv")
    edges = {s: [(m, t) for m in range(14) if g.get(t := step(s, m)) == d + 1]
             for s, d in g.items()}
    low = bytes([7, 9, 5, 11, 3, 7, 4])
    high = bytes([7, 9, 3, 7, 4, 11, 2])
    paths = {}

    def visit(s, moves, peak):
        if s == S:
            if len(moves) != 41 or moves in paths:
                raise ValueError("Unexpected terminal sequence")
            paths[moves] = peak
            return
        for m, t in edges[s]:
            visit(t, moves + bytes([m]), max(peak, height(t)))

    visit(A, b"", height(A))
    within28 = {ms for ms, p in paths.items() if p <= 28}
    within29 = {ms for ms, p in paths.items() if p <= 29}
    additional = within29 - within28
    if (len(paths), len(within28), len(within29), len(additional)) != (106036, 71412, 106036, 34624):
        raise ValueError("Counts differ from the deposited layers")
    if any(not ms.startswith(high) for ms in additional):
        raise ValueError("Unexpected prefix in the new sequences")
    companions = {low + ms[len(high):] for ms in additional}
    if len(companions) != len(additional) or any(paths.get(ms) != 27 for ms in companions):
        raise ValueError("Missing or repeated peak-27 companion")
    print("Recorded 41-move sequences at cap 28: 71412")
    print("Recorded 41-move sequences at cap 29: 106036")
    print("Extra sequences with the high prefix: 34624")
    print("Distinct recorded companions of peak 27 with the same suffix: 34624")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without Python optimization.")
    main()
