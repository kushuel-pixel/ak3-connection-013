"""Emit small kernel-checkable backward counts for the supplied 42 layers."""
import argparse
import sys
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("review", type=Path, help="extracted kit 012")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    sys.path.insert(0, str(args.review / "stages/010"))
    from verify import A, S, height, run

    layers = [[] for _ in range(42)]
    for line in (args.review / "stages/008/vertices29.tsv").read_text().splitlines():
        depth, a, b = line.split("\t")
        if any(c not in "xXyY" for c in a+b):
            raise ValueError(line)
        layers[int(depth)].append((a, b))
    assert layers[0] == [A] and layers[-1] == [S]
    assert sum(map(len,layers)) == len(set(v for l in layers for v in l)) == 159

    out = ["import PathCount", "", "namespace Candidate.AK3Peak.FixedS", "open Verify.AtomicSemantics", ""]
    for d, layer in enumerate(layers):
        literals = ",\n   ".join(f'(w! "{a}", w! "{b}")' for a, b in layer)
        out.extend([f"private def layer{d} : List WordState :=", f"  [{literals}]", ""])
    for d in reversed(range(42)):
        tail = f"rest{d+1}" if d < 41 else "[]"
        out.append(f"private def rest{d} := layer{d} :: {tail}")
    out += ["", "def recordedLayers := rest1", "", "theorem layer_count : recordedLayers.length = 41 := by decide +kernel", ""]
    for cap in [27, 28, 29]:
        counts = {}
        for d in reversed(range(42)):
            if cap == 27 and d < 7:
                break
            next_counts = counts
            counts = {s: (int(s == S) if d == 41 else
                       sum(next_counts.get(run(s,[m])[-1],0) for m in range(14)))
                      if height(s) <= cap else 0 for s in layers[d]}
            nums = ", ".join(str(counts[s]) for s in layers[d])
            name = f"c{cap}_{d}"
            out.extend([f"private def {name} : Counts := layer{d}.zip [{nums}]",
                        f"private theorem ok{cap}_{d} : table {cap} rest{d} = {name} := by"])
            if d < 41:
                out.extend([f"  change propagate {cap} layer{d} (table {cap} rest{d+1}) = _",
                            f"  rw [ok{cap}_{d+1}]"])
            out.extend(["  decide +kernel",""])
        if cap == 27:
            assert counts[("YXYYxyyyyyX", "xxYYYYYXYxyyyyyX")] == 34624
        else:
            assert counts[A] == {28:71412,29:106036}[cap]
    out += ["theorem recorded_counts : countFrom 28 recordedLayers ak3 = 71412 ∧ countFrom 29 recordedLayers ak3 = 106036 := by",
        "  have c : ways (table 28 (layer0 :: recordedLayers)) ak3 = 71412 ∧",
        "      ways (table 29 (layer0 :: recordedLayers)) ak3 = 106036 := by",
        "    change ways (table 28 rest0) ak3 = _ ∧ ways (table 29 rest0) ak3 = _",
        "    rw [ok28_0, ok29_0]", "    decide +kernel",
        "  simpa only [table_correct, ite_eq_left (by decide +kernel : ak3 ∈ layer0)] using c", "",
        "def suffixLayers := rest8",
        "theorem suffix_depths : suffixLayers.length = 34 := by decide +kernel",
        "theorem shared_suffix_count :",
        '    countFrom 27 suffixLayers (w! "YXYYxyyyyyX", w! "xxYYYYYXYxyyyyyX") = 34624 := by',
        '  let j : WordState := (w! "YXYYxyyyyyX", w! "xxYYYYYXYxyyyyyX")',
        "  have c : ways (table 27 (layer7 :: suffixLayers)) j = 34624 := by",
        "    change ways (table 27 rest7) j = _",
        "    rw [ok27_7]",
        "    decide +kernel",
        "  simpa only [table_correct, ite_eq_left (by decide +kernel : j ∈ layer7)] using c", "",
        "end Candidate.AK3Peak.FixedS", ""]
    args.output.write_text("\n".join(out))


if __name__ == "__main__":
    main()
