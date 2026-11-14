import Submission.Connections
import Submission.SixMixFinite
open Verify Verify.AtomicSemantics Verify.EntryExtension
example : Verify.Submission.SixMixFinite.count Verify.Submission.SixMixFinite.unit = 245 := by decide +kernel
