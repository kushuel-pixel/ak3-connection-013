"""Render intermediate literal states from the pinned reviewer ZIP for Lean."""
import argparse
import json
import re
import sys
from pathlib import Path


def literal(state):
    a, b = state
    if any(c not in "xXyY" for c in a + b):
        raise ValueError(state)
    return f'(w! "{a}", w! "{b}")'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("review", type=Path, help="extracted review kit 012")
    parser.add_argument("output", type=Path)
    parser.add_argument("--through", action="store_true", help="render the cap-25 certificate that traverses the old edge")
    opts = parser.parse_args()
    evidence = opts.review / "stages/010"
    sys.path.insert(0, str(evidence))
    from verify import A, S, run
    from sair_verifier.core import INVERSE_MOVE

    if opts.through:
        ref = json.loads((opts.review / "stages/006/bridge41.json").read_text())
        moves = ref["moves"]
        states = run(A, moves)
        assert list(map(list, states)) == ref["states"]
        rs = ",\n   ".join(f"(.m{m}, {literal(v)})" for m,v in zip(moves,states[1:]))
        out = ["import FixedSWitness","","namespace Candidate.AK3Peak.FixedS","open Verify.AtomicSemantics","",
               "private def throughRows : Rows :=",f"  [{rs}]","",
               "def through25 := throughRows.map Prod.fst","",
               "theorem through25_ok : through25.length = 41 ∧ Witness 25 ak3 source through25 ∧",
               "    peak through25 ak3 = 25 ∧ avoids through25 ak3 = false := by",
               "  obtain ⟨he,hp,ha⟩ := trace_sound (s := ak3) (rs := throughRows) (by decide +kernel)",
               "  exact ⟨by decide +kernel, ⟨he.trans (by decide +kernel),hp.le.trans (by decide +kernel)⟩,",
               "    hp.trans (by decide +kernel),ha.trans (by decide +kernel)⟩","",
               "theorem through25_move35 : (through25.take 34).length = 34 ∧",
               "    wordRun (through25.take 34) ak3 = U ∧ through25[34]? = some .m4 ∧ wordStep .m4 U = V := by",
               "  have ok : traceOK ak3 (throughRows.take 34) = true := by decide +kernel",
               "  have hd := (trace_sound ok).1",
               "  rw [List.map_take] at hd",
               "  exact ⟨by decide +kernel,hd.trans (by decide +kernel),by decide +kernel,by decide +kernel⟩",
               "", "end Candidate.AK3Peak.FixedS",""]
        opts.output.write_text("\n".join(out))
        return
    sequences = {}
    for h in (22, 23):
        row = json.loads((evidence / f"search{h}.jsonl").read_text().splitlines()[-1])
        sequences[h] = row["moves"]
    text = (opts.review / "FORM_DESCRIPTION.txt").read_text()
    numbers, = re.findall(r"^((?:[0-9]+ )+[0-9]+)$", text, re.M)
    sequences[25] = list(map(int, numbers.split()))
    assert sequences[25] == json.loads((evidence / "bypasses.json").read_text())["25"]
    out = ["import FixedSWitness", "", "namespace Candidate.AK3Peak.FixedS", "open Verify.AtomicSemantics", ""]
    for cap, moves in sequences.items():
        for name, start, end, ms, term1, term2 in [
            (f"bypass{cap}", A, S, moves, "ak3", "source"),
            (f"back{cap}", S, A, [INVERSE_MOVE[m] for m in reversed(moves)], "source", "ak3")]:
            states = run(start, ms)
            assert states[-1] == end
            rows = ",\n   ".join(f"(.m{m}, {literal(s)})" for m, s in zip(ms, states[1:]))
            out += [f"private def {name}Rows : Rows :=", f"  [{rows}]", "",
                    f"def {name} : List Move := {name}Rows.map Prod.fst", "",
                    f"theorem {name}_ok : {name}.length = {len(ms)} ∧ peak {name} {term1} = {cap} ∧",
                    f"    AvoidWitness {cap} {term1} {term2} {name} :=", f"  certified {name}Rows (by decide +kernel)", ""]
        out += [f"theorem back{cap}_inverse : back{cap} = reverseMoves bypass{cap} := by decide +kernel", ""]
    cyc = json.loads((opts.review / "S_SIDE_CYCLE.json").read_text())
    out += [f"def lowP : WordState := {literal(cyc['p'])}", f"def lowQ : WordState := {literal(cyc['q'])}", ""]
    access = cyc["S_to_p_moves"]
    rows = ",\n   ".join(f"(.m{m}, {literal(s)})" for m, s in zip(access, run(S, access)[1:]))
    out += ["private def approachRows : Rows :=", f"  [{rows}]", "def approach := approachRows.map Prod.fst",
            "theorem approach_ok : Witness 27 source lowP approach := by",
            "  obtain ⟨he,hp,_⟩ := trace_sound (s := source) (rs := approachRows) (by decide +kernel)",
            "  exact ⟨he.trans (by decide +kernel), hp.le.trans (by decide +kernel)⟩", "",
            "end Candidate.AK3Peak.FixedS", ""]
    opts.output.write_text("\n".join(out))


if __name__ == "__main__":
    main()
