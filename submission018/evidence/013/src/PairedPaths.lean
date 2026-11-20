import CountSemantics
import FixedSCycles

namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics

def firstTwo : List Move := [.m7,.m9]

private theorem prefix_ok :
    Witness 27 ak3 fork firstTwo ∧ (firstTwo ++ arm27).length = 7 ∧
    (firstTwo ++ arm29).length = 7 ∧ peak (firstTwo ++ arm27) ak3 = 27 ∧
    peak (firstTwo ++ arm29) ak3 = 29 ∧ firstTwo ++ arm27 ≠ firstTwo ++ arm29 := by
  unfold Witness
  decide +kernel

/-- Each distinct continuation gives a peak-27 path and a peak-29 path of 41 moves. -/
theorem paired_34624 :
    ∃ tails : List (List Move), tails.Nodup ∧ tails.length = 34624 ∧ ∀ ys ∈ tails,
      let a := (firstTwo ++ arm27) ++ ys
      let b := (firstTwo ++ arm29) ++ ys
      a ≠ b ∧ a.length = 41 ∧ b.length = 41 ∧ wordRun a ak3 = source ∧
      wordRun b ak3 = source ∧ peak a ak3 = 27 ∧ peak b ak3 = 29 := by
  refine ⟨listsOn 27 suffixLayers joinState,listsOn_nodup _ _ _,
    (listsOn_length _ _ _).trans shared_suffix_count,?_⟩
  intro ys hy
  obtain ⟨len, endS, cap⟩ := listed_path hy
  have n := len.trans suffix_depths
  obtain ⟨hw,ln,hn,lp,hp,ne⟩ := prefix_ok
  obtain ⟨old,new,_⟩ := both_branches
  have leq := (witness_append hw old).1
  have heq : wordRun (firstTwo ++ arm29) ak3 = joinState := by
    rw [run_append, hw.1, new.1]
  dsimp only
  refine ⟨fun he => ne (List.append_cancel_right he), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_append,ln,n]
  · rw [List.length_append,hn,n]
  · rw [run_append,leq,endS]
  · rw [run_append,heq,endS]
  · rw [peak_append,lp,leq,max_eq_left cap]
  · rw [peak_append,hp,heq,max_eq_left (by omega : peak ys joinState ≤ 29)]

end Candidate.AK3Peak.FixedS
