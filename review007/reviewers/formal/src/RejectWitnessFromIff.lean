import Submission.Connections
import Submission.SixMixFinite
open Verify Verify.AtomicSemantics Verify.EntryExtension
example (n : Nat) : Reach Verify.Submission.Connections.ak3 (Verify.Submission.EFamily.initial n) := Verify.Submission.Connections.ak3_E_iff_hit n
