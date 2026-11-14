import Submission.Connections
import Submission.SixMixFinite
open Verify Verify.AtomicSemantics Verify.EntryExtension
example : Verify.Submission.SixMixFinite.product 1 63 = ⟨6,1,5,1⟩ := by decide +kernel
