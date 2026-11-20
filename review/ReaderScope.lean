import ExitTransfer
import RecordedPeak29

namespace Candidate.AK3Peak.FixedS.ReaderScope
open Verify.AtomicSemantics ExitTransfer

example : Reaches 28 source E3 ↔ Reaches 28 ak3 standard := exit_iff 28 (by decide)

example (h : ¬ Reaches 28 ak3 standard) : ¬ Reaches 28 source E3 := excluded_at_28_of_ak3 h

/-- The cited exclusion cannot be used as a proof with its hypothesis removed. -/
example : True := by
  fail_if_success
    have _overclaim : ¬ Reaches 28 source E3 := excluded_at_28_of_ak3
  trivial

example : peak arm29 fork = 29 := by decide +kernel

/-- Test that the check rejects the wrong cap for this specific arm. -/
example : True := by
  fail_if_success
    have _wrongPeak : peak arm29 fork = 28 := by decide +kernel
  trivial

example (ms : List Move) :
    (ms ∈ listsOn 29 recordedLayers ak3 ∧ ms ∉ listsOn 28 recordedLayers ak3) ↔
    ∃! ys, ys ∈ RecordedPeak29.tails ∧ ms = RecordedPeak29.highPrefix ++ ys :=
  RecordedPeak29.new_at_29_iff ms

end Candidate.AK3Peak.FixedS.ReaderScope
