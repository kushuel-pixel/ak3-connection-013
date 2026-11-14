import Submission.Connections
import Submission.SixMixFinite
open Verify Verify.AtomicSemantics Verify.EntryExtension
example (n : Nat) : groupRun (Verify.Submission.EFamily.word n) (Verify.Submission.EFamily.initial n) = (y,x) := Verify.Submission.EFamily.reaches n
