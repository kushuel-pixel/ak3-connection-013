# Replaying the fixed-target Lean supplement

The project retains the ordered words, move type, free reduction, inverse moves, endpoints and peak semantics of ACC-P000024. It runs on Linux with the pinned Lean 4.35.0 binaries, Lake, leanc, Git and Python 3. An existing build of the identical baseline can also be used.

## Set up the pinned baseline

Starting in the directory containing this guide, run these commands once. Keep Lean and leanc from the same toolchain on PATH when invoking the Python driver. The baseline directory includes the original Lake manifest and toolchain pin.

```sh
cd pinned
lake exe cache get Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
lake build
cd ..
```

With elan, run the driver from inside the pinned directory so both executables use the local toolchain pin.

```sh
cd pinned
python3 -B ../replay.py kernel /tmp/ak3-fixed-s-kernel
```

The output directory must be new. Each successful run leaves stage logs, compiled modules, timings and an axiom report there. To use an existing built copy of the baseline, supply its directory as `--project PATH`. The runner compares source bytes, package revisions and the compiler commit. To check all results, choose `all` instead of `kernel` and supply a fresh output path.

| Mode | Checks |
|---|---|
| kernel | Literal witnesses and their inverses, old-edge avoidance, two simple cycles, the identity of the two five-move branches for any reduced input, layer-constrained path counts, and soundness of the finite search procedures. |
| through24 | Adds the actual cap-22 edge-deleted and cap-24 ordinary ball calculations, then checks the resulting exact distances and the threshold for reaching S within 41 moves. |
| through26 | Additionally regenerates the ordinary cap-26 balls and checks the exact distances for caps 25 and 26. |
| cap30-pilot | Adds the partial cap-30 computation at radii 8 and 15, which excludes paths through length 23. |
| all | All of the above. The full ordinary cap-30 split at radii 16 and 24 remains a separate obligation. |

The two larger searches run consecutively. Source review and the short witness/cycle/count proofs need only the first mode. Replay rejects unexpected axioms in every audited declaration. The native runs compile the supplied Lean searches to shared objects. Full key comparisons resolve hash collisions in all variants. The banked variant keeps overflow keys and has a Lean proof of equivalence to the compact set representation. Its small pilot exercises empty slots, collisions and positive and negative intersections.

## Results of the author replay

For the two fixed endpoints, the ordinary and edge-avoiding distances are respectively 42 and 44 at cap 22, both 42 at caps 23 and 24, and both 41 at caps 25 and 26. Every cap-22 path of at most 43 moves crosses the old common edge. At cap 25 there are shortest paths of both kinds: one avoids that edge, and one traverses it on move 35. Each lower-bound run uses one audited native computation axiom for that run. The cap-26 ordinary split at 16+24 took 1,874.75 seconds with peak resident memory of 4,890,528 KiB. At cap 30 the separate 8+15 split certifies a lower bound of 24 moves. The 41-move upper bound still applies. The stronger exclusion through length 40 at caps 27 to 30 is supported by the earlier C++ enumeration and awaits the full Lean calculation.

## What the path counts certify

The list includes 159 literal states at 42 depths (depth 0 through 41) from the submitted cap-29 graph. At each depth the suffix count branches over the 14 distinct move IDs. Each successor must belong to the next listed layer. At the final depth the endpoint must be S. The kernel checks every row against the already checked counts for the next depth. The final theorems construct lists of pairwise distinct move-ID sequences of the stated length and peak. They also construct 34,624 distinct 34-move suffixes that can be attached to either seven-move prefix, giving paired paths of exact peaks 27 and 29. Exactness of the count among *all* shortest paths in the unrestricted set of graph vertices needs a completeness proof for the listed layers and exclusion of shorter paths at cap 29.

## Reconstruct the embedded input

The literal witnesses and vertex list are embedded in the Lean sources. To regenerate them from an extracted review kit 012, use these optional commands from the supplement root.

```sh
python3 -B generate_rows.py /path/to/review-kit /tmp/FixedSPaths.lean
cmp /tmp/FixedSPaths.lean src/FixedSPaths.lean
python3 -B generate_rows.py --through /path/to/review-kit /tmp/ThroughEdge.lean
cmp /tmp/ThroughEdge.lean src/ThroughEdge.lean
python3 -B generate_counts.py /path/to/review-kit /tmp/RecordedCounts.lean
cmp /tmp/RecordedCounts.lean src/RecordedCounts.lean
```

The review kit ZIP has SHA-256 `bd0326a934df83ff44dfc8f90b2bc1ca71066a86196f709ae75e8eed89d2f6ba`. The generators supply proposed intermediate values. Lean recomputes the transitions and counts from its word semantics.

## Checking the saved cap-30 layers

The original stage 009 workers deposited 64 shard receipts per depth. The new cover certificate uses the root and the next two A layers (158 states) and the root and the next three S layers (344 states). The generator checked all 448 file sizes and SHA-256 digests for these seven layers. It decoded the proposed states and re-encoded them as Lean keys. Lean checked the roots and every admissible transition from the interior depths against the supplied rows. Consequently every state reachable within these radii is covered, independently of how the input lists were generated. To repeat the conversion, use the stage 009 code to regenerate the two small sets of shard files, then run

```sh
python3 -B generate_layer_pilot.py /path/to/stages/009 /path/to/A30 /path/to/S30 /tmp/LayerPilot.lean
cmp /tmp/LayerPilot.lean src/LayerPilot.lean
```

The fixed-cap theorem in `StreamCut.lean` specifies how complete root coverage and the final streamed A-side move suffice for the full 16+24 lower bound. The pilot only instantiates the stated early radii. The ordinary 8+15 cap-30 result is a separate native run, independent of the shard inputs.

## Source pins

- The baseline project comes from the author's ACC-P000024 review repository at commit `4e8a0096c1d2eb38b228bf2187ef691afff90017`, directory `submissions/bridge42/lean`. The Lean compiler commit is `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The mathlib revision is `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- `B5BallEngine.lean` and `B5BallSearch.lean` are unchanged members of `submissions/bridge42-45/native-replay.zip` at the same commit. The archive SHA-256 is `df2a4b5152af78a2331d653d3f5ee57025642268653e79831d53f77a262cfc9d`. They supply the previous encoder and its agreement with mathlib's free-group moves.
- New sources begin with `FixedSWitness.lean`. `CompactSound.lean` proves the new mixed-radix encoding preserves the full state and the searches cover every admissible path. `BankSound.lean` proves the collision-handling storage variant refines that same search. `CountSemantics.lean` supplies distinct move lists behind the numeric counts. The old result's native distance theorem is unnecessary for the new distance proofs.

AI assistance was used in the implementation, checks and drafting.
