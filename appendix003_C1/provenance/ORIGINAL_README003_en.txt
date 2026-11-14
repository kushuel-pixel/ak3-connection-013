AK3 CONNECTION SUBMISSION - ENGLISH PROOF APPENDIX 003
13 November 2026

Read AK3_4mix_6mix_Proof_Appendix_003_en.pdf first.
The matching .tex file is the editable mathematical source.

RESULTS AND SCOPE
The endpoints are the exact ordered pairs
S=(XyyyxYYYY,xxYYYYYXyyyyy), E0=(Y,xxYXy).
Uppercase letters denote inverses. The fixed fourteen atomic moves are
listed in the appendix. There is no total-word-length cap in these results.

1. Exactly four mix moves: every S-to-E0 path has at least 24 atomic moves.
2. Exactly six mix moves: sixteen residual layouts, with 156 I and 16 -I
   normalized sign profiles. The -I case needs odd inversion counts on both
   rows; at total length <=23 it permits at most 15 conjugation moves.

These are scoped statements. In particular, this package supplies neither
an S-to-exit path nor an exclusion of all six-mix or eight-plus-mix paths.

VERIFICATION STATUS
Earlier mathematical inputs and source001's new 34 Lean declarations were
accepted in independent AI reviews. Appendix003 is a new English
consolidation: separate independent review of this text is still pending.
There are no new Lean proofs or Lean executions in this preparation.
The existing SixMixFinite Lean module proves the finite matrix inventory;
it does not prove the complete arbitrary-path theorem by itself.

This preparation freshly checked all four explicit group images, both
inverse substitutions per model, all four common-word witnesses, the S10
quotient, all 256 four-mix and 4096 six-mix matrix cases, and all 3364
dual-column equalities in eight central certificates. It also recompiled
and replayed the preserved review028 negative B15 scanner and all three
partitions of the review055 positive B15 scanner. Outputs matched the
reviewed census: positive zero common classes; negative five, four <=32.

REPRODUCE
First run: python3 checkers/check_manifest.py
Then run:  python3 checkers/check_appendix.py
Optional full replay: python3 checkers/replay_B15.py

The small checker needs only Python 3 standard library. Full replay needs
Linux and g++ (C++17). Each scanner child has a 4 GiB address-space limit,
CPU soft/hard limits 90/91 seconds, and a 150-second wall timeout. Runs are
sequential. A timeout is an incomplete replay, not a mathematical failure.
The reproduction scripts overwrite their respective verification outputs;
elapsed times will change their hashes. Verify the manifest before running.

The C++ scanners in checkers/ are byte-preserved historical independent
implementations. Replaying them in preparation003 is an author-side replay,
not a new independent review of the English exposition.

PDF BUILD
On a normal TeX Live installation:
pdflatex -interaction=nonstopmode -halt-on-error AK3_4mix_6mix_Proof_Appendix_003_en.tex
Repeat until references and contents are stable (normally twice).
Dependencies: standard article, geometry, lmodern, amsmath, amssymb,
amsthm, booktabs, longtable, array, microtype, xcolor, fancyhdr, enumitem,
hyperref. The three pdfmapfile commands explicitly select standard font
maps so the document also builds in a minimal map configuration.

EVIDENCE
data/: exact matrix profiles, common words, group maps, and eight duals.
checkers/: short direct checker, preserved scanners, and replay driver.
verification/: exact fresh output and raw full-scan output.
provenance/: extraction hashes, fixed independent review records,
            corrected HNN convention, and full Lean declaration mapping.
lean/Submission/SixMixFinite.lean: byte-preserved finite-inventory module
from source001, already audited in review002; no new Lean replay here.

NEXT REVIEW
Check the English proofs against the data, especially common-product
orientation, original-path cost accounting, the HNN shift r=s+4, the
unbounded-witness shortening lemma, the 16-layout boundary, and the
distinction between a finite Lean inventory and a full path theorem.

RELEASE
No external publication or submission was performed. This is review
material. Public repository commit, reference reconciliation, and final
license/attribution decisions belong to the later release stage.
