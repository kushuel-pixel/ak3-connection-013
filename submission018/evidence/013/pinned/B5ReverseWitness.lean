import B5PeakCore

namespace Candidate.AK3Peak
open Verify.AtomicSemantics

/-- Canonical representatives make evaluation injective on reduced states. -/
theorem reduced_eq_of_eval {s t : WordState} (hs : ReducedState s) (ht : ReducedState t)
    (h : evalState s = evalState t) : s = t := by
  let canonical (g : GroupState) : WordState := (FreeGroup.toWord g.1, FreeGroup.toWord g.2)
  calc
    s = canonical (evalState s) := wordRun_canonical [] s hs
    _ = canonical (evalState t) := congrArg canonical h
    _ = t := (wordRun_canonical [] t ht).symm

def inverseAtom : Move → Move
  | .m0 => .m0 | .m1 => .m1 | .m2 => .m3 | .m3 => .m2
  | .m4 => .m5 | .m5 => .m4 | .m6 => .m7 | .m7 => .m6
  | .m8 => .m9 | .m9 => .m8 | .m10 => .m11 | .m11 => .m10
  | .m12 => .m13 | .m13 => .m12

def reverseMoves : List Move → List Move
  | [] => []
  | m :: ms => reverseMoves ms ++ [inverseAtom m]

theorem undo_word_step (m : Move) (s : WordState) (hs : ReducedState s) :
    wordStep (inverseAtom m) (wordStep m s) = s := by
  apply reduced_eq_of_eval (wordStep_reduced _ _ (wordStep_reduced m s hs)) hs
  simp only [eval_wordStep]
  generalize evalState s = g
  rcases g with ⟨a, b⟩
  cases m <;> simp [inverseAtom, groupStep, Verify.X, Verify.Y, mul_assoc]

/-- The reverse list visits the original states in reverse order, within the same cap. -/
theorem witness_reverse {C : ℕ} {s t : WordState} {ms : List Move}
    (hs : ReducedState s) (w : Witness C s t ms) : Witness C t s (reverseMoves ms) := by
  induction ms generalizing s t with
  | nil =>
    rcases w with ⟨he, hb⟩
    change s = t at he
    subst t
    exact ⟨rfl, hb⟩
  | cons m ms ih =>
    rcases w with ⟨he, hb⟩
    change max (total s) (peak ms (wordStep m s)) ≤ C at hb
    have tailW : Witness C (wordStep m s) t ms := ⟨he, (max_le_iff.mp hb).2⟩
    have undo := undo_word_step m s hs
    have one : Witness C (wordStep m s) s [inverseAtom m] := by
      constructor
      · exact undo
      · change max (total (wordStep m s)) (total (wordStep (inverseAtom m) (wordStep m s))) ≤ C
        rw [undo]
        exact max_le (le_trans (source_le_peak ms _) (max_le_iff.mp hb).2)
          (max_le_iff.mp hb).1
    exact witness_append (ih (wordStep_reduced m s hs) tailW) one

end Candidate.AK3Peak
