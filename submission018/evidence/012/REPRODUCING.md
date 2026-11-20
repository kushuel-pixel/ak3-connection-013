# Reproducing the fixed-target result

From the extracted review kit, the following commands check file integrity and run the portable replay. In the source repository, run the Python command from the directory containing this guide. The kit includes the Python and C++ sources, literal witnesses, compact shortest-path graphs, search logs, native layer records and the license of the included organizer-verifier code. The multi-gigabyte search balls can be regenerated with the commands below.

```sh
sha256sum -c SHA256SUMS
python3 -B verify_submission.py
```

The lightweight replay uses Python 3.12 and its standard library. It checks the move IDs printed in the form directly, both directions of the ordinary and edge-avoiding witnesses, the six-move example, the ten-edge cycle and the saved counting and search records. The last line should read `PASS fixed-target submission replay`. Run without Python optimization. A quick pass checks the stored evidence. Regenerating the breadth-first balls gives a fresh test of completeness.

| Claim | Primary files under stages/ |
|---|---|
| Cap-22 baseline | 006/bridge42.json, 006/alternate22.jsonl, 007/cap22_dag.json |
| First improvement at cap 25 | 006/alternate24.jsonl, 010/bypasses.json |
| Avoiding the old edge at caps 22 and 23 | 010/search22.jsonl, 010/search23.jsonl, 010/alternate22.json, 010/alternate23.json |
| Exclusion through 40 moves at cap 30 | 009/forward30.json, 009/reverse30.json, 009/shardsA30.json, 009/shardsS30.json |
| Shortest sequences and five-move substitution | 007/explicit_check.json, 008/geodesics29.json, 008/vertices29.tsv, 008/branch.py |

## Rebuild the distance bounds

Commands below use Bash on 64-bit Linux and a C++17 compiler with OpenMP. Start each block in the specified stage directory within the kit or the repository. Commands may need substantial memory. For cap 30, allow tens of GiB of working disk. The generator writes 64 shards per layer and can resume completed layers. Use separate directories for the two endpoint balls and run the sides successively.

**Ordinary cap 24.** In `stages/006`, build the two complete balls. Expect radii 15 and 26, sizes 19,354,365 and 32,672,025, and zero hits.

```sh
g++ -std=c++17 -O3 check_split.cpp -o check_split
./check_split endpoints.tsv 24 15 26
```

**Deleting e.** In `stages/010`, the enumerator omits U–V in both directions. The first two runs should return zero hits. The last two recover positive paths of 44 and 42 moves. An incomplete run or a state-budget stop cannot certify nonintersection.

```sh
g++ -std=c++17 -O3 check_split.cpp -o check_split
./check_split endpoints.tsv 22 17 26
./check_split endpoints.tsv 23 16 25
g++ -std=c++17 -O3 search.cpp -o search
./search endpoints.tsv 22 44 160000000
./search endpoints.tsv 23 44 230000000
```

**Ordinary cap 30.** In `stages/009`, build the two inner balls and test their outer boundaries. Both streaming searches should report empty match lists. The reverse program takes S as its first argument, so its output radii are in S,A order. The reverse test uses alternate arithmetic on the streamed boundary and reuses the stored inner balls.

```sh
g++ -std=c++17 -O3 -fopenmp layers.cpp -o layers
./layers endpoints.tsv 30 0 15 work/A 68000000 4
./layers endpoints.tsv 30 1 24 work/S 76000000 6
g++ -std=c++17 -O3 -fopenmp stream_join.cpp -o forward
g++ -std=c++17 -O3 -fopenmp -DLOW_ARITHMETIC stream_join.cpp -o reverse
./forward 30 work/A work/S 15 24 work/candidates_A 7
./reverse 30 work/S work/A 24 15 work/candidates_S 7
```

## Rebuild the cap-29 shortest-path graph

In `stages/008`, build the balls and compare the recovered midpoints and shortest-path vertices with the deposited lists. The 16+24 intersection is empty. The 16+25 intersection has two vertices. The final pair of audit runs check completeness of the stored layers under a second implementation of the word operations. The recovered graph has 159 vertices, 295 directed labelled edges and 106,036 shortest sequences.

```sh
g++ -std=c++17 -O3 -fopenmp layers.cpp -o layers
g++ -std=c++17 -O3 -fopenmp join.cpp -o join
g++ -std=c++17 -O3 -fopenmp trace.cpp -o trace
g++ -std=c++17 -O3 -fopenmp audit_layers.cpp -o audit_layers
./layers endpoints.tsv 29 0 16 work/A 95000000 7
./layers endpoints.tsv 29 1 25 work/S 95000000 7
./join work/A work/S 16 24 3 out40.tsv
./join work/A work/S 16 25 5 out41.tsv
./trace work/A work/S out41.tsv 29 16 rebuilt.tsv
diff <(sort meet29_40.tsv) <(sort out40.tsv)
diff <(sort meet29.tsv) <(sort out41.tsv)
diff <(sort vertices29.tsv) <(sort rebuilt.tsv)
./audit_layers endpoints.tsv 29 0 16 work/A 130000000 7
./audit_layers endpoints.tsv 29 1 25 work/S 130000000 7
python3 -B check_logs.py
python3 -B branch.py
```

The depth and both relator words identify a row in the vertex list. The Python analysis rebuilds labelled edges by applying the moves, counts prefixes and suffixes in depth order, and counts paths that stay below height 29. A fresh all-layer rerun at cap 29 uses about 24 GiB just for the raw balls.
