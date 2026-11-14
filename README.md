# AK(3) connection problem · submission 013

Hiromu Yasuno · 14 November 2026 · Partial result

A known 42-move sequence reaches the fixed state S. The entry theorem lets a search continue to the standard pair once it reaches a unimodular pair satisfying the single-occurrence condition. For paths from S to E₀, exactly four mixes require at least 24 moves, and exactly six mixes restrict the row layout to sixteen possibilities. Finding a path from S to an exit remains open.

| To inspect | Start here |
|---|---|
| Manuscript and proof appendix | [Combined PDF, 22 pages](AK3_CONNECTION_SUBMISSION_FINAL_013_en.pdf) · [English manuscript](PAPER_EN.md) |
| The ten claims and their evidence | [Claim map](CLAIMS.md) · [34 Lean declarations and their scope](LEAN_DECLARATIONS.json) |
| Lean source | [Entry theorem](sources/submission001/lean/Extension/FourWay.lean) · [E-family construction](sources/submission001/lean/Submission/EFamily.lean) · [Reachability](sources/submission001/lean/Submission/Connections.lean) · [Six-mix inventory](sources/submission001/lean/Submission/SixMixFinite.lean) |
| Finite evidence | [Appendix source](appendix003_C1/AK3_4mix_6mix_Proof_Appendix_003_C1_en.tex) · [Certificates](appendix003_C1/data/) · [Scanners and checkers](appendix003_C1/checkers/) |
| Reproduction | [Commands and dependencies](REPRODUCING.md) · [Checks on the Git snapshot](VERIFICATION.md) |
| Submission text and provenance | [Title](FORM_TITLE.txt) · [Description](FORM_DESCRIPTION.txt) · [Public edition and source identity](PROVENANCE.md) · [Source notices](NOTICE.md) |

## Apply the entry theorem

The example from candidate 013 has determinant −1 and a single occurrence of y in its second relator.

```lean
import Extension.FourWay
open Verify Verify.AtomicSemantics Verify.EntryExtension

def candidate : GroupState := (x^3 * y^2, x^2 * y)

example : Reach candidate (x, y) :=
  four_way_to_standard candidate (by decide +kernel) (by decide +kernel)
```

The complete statement of Theorem B is on main page 3. The formal proofs cover the E-family endpoint and move count, entry and connection results, and the finite matrix inventory. The peak bound for the displayed construction and the passage from the finite checks to arbitrary paths use the hand proofs.

日本語で始める場合は[再現手順](REPRODUCING.md)へ。提出用PDFは本文8頁・付録14頁。14手の操作表は本文1頁、定理Bは本文3頁に収録しています。
