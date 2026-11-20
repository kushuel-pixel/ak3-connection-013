"""Replay the printed certificate, local example and finite-search evidence."""
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
STAGES = HERE / "stages" if (HERE / "stages").is_dir() else HERE.parent / "stages"
SCRIPTS = {
    "006": ("verify.py", "audit_logs.py"),
    "007": ("audit.py",),
    "008": ("check_logs.py",),
    "009": ("check.py",),
    "010": ("verify.py",),
}


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def check_printed_witness():
    sys.path.insert(0, str(STAGES / "010"))
    from verify import A, S, U, V, height, run
    from sair_verifier.core import INVERSE_MOVE

    paragraphs = (HERE / "FORM_DESCRIPTION.txt").read_text(encoding="utf-8").split("\n\n")
    certificates = [p.split() for p in paragraphs if p.split() and all(w.isdecimal() for w in p.split())]
    tokens, = certificates
    moves = list(map(int, tokens))
    assert moves == read_json(STAGES / "010/bypasses.json")["25"]
    path = run(A, moves)
    assert (len(moves), path[-1], max(map(height, path))) == (41, S, 25)
    assert all((a, b) not in ((U, V), (V, U)) for a, b in zip(path, path[1:]))
    assert run(S, [INVERSE_MOVE[i] for i in reversed(moves)]) == path[::-1]
    print("PASS printed 41-move certificate, peak 25, both directions, e avoided", flush=True)

    cycle = read_json(HERE / "S_SIDE_CYCLE.json")
    p, q = tuple(cycle["p"]), tuple(cycle["q"])
    approach = run(S, cycle["S_to_p_moves"])
    assert approach[-1] == p and max(map(height, approach)) <= 27
    left, right = [run(p, ops) for ops in cycle["arms"]]
    assert set(left) & set(right) == {p, q}
    assert left[-1] == right[-1] == q
    assert list(map(height, left)) == list(map(height, right)) == [21, 28, 28, 21]
    loop = run(p, cycle["arms"][0] + [INVERSE_MOVE[i] for i in reversed(cycle["arms"][1])])
    assert loop == left + right[-2::-1] and len(set(loop[:-1])) == 6
    assert cycle["direct"] == [1] and run(p, [1]) == [p, q]
    print("PASS S-side approach at cap 27, two three-move arms and one-move descent-state link", flush=True)


def main():
    if not __debug__:
        raise SystemExit("Run without Python optimization.")
    check_printed_witness()
    for stage, scripts in SCRIPTS.items():
        for script in scripts:
            subprocess.run([sys.executable, "-B", script], cwd=STAGES / stage, check=True)
    print("PASS fixed-target submission replay")


if __name__ == "__main__":
    main()
