import Submission.Connections
import Submission.SixMixFinite
open Verify Verify.AtomicSemantics Verify.EntryExtension
example (n : Nat) : (Verify.Submission.EFamily.word n).length = 3*n+11 := Verify.Submission.EFamily.word_length n
