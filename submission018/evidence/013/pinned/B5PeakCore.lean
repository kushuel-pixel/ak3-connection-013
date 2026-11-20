import Verify.AtomicSemantics

namespace Candidate.AK3Peak
open Verify.AtomicSemantics
open Verify.ReducedWords (xLetter XLetter yLetter YLetter)

def ak3 : WordState :=
  ([xLetter, yLetter, xLetter, YLetter, XLetter, YLetter],
   [xLetter, xLetter, xLetter, YLetter, YLetter, YLetter, YLetter])

def relator : Word :=
  [XLetter, yLetter, yLetter, yLetter, xLetter, YLetter, YLetter, YLetter, YLetter]

def source : WordState :=
  (relator, [xLetter, xLetter, YLetter, YLetter, YLetter, YLetter, YLetter,
             XLetter, yLetter, yLetter, yLetter, yLetter, yLetter])

def total (s : WordState) : ℕ := s.1.length + s.2.length

/-- Empty paths still visit their start. Nonempty paths also visit their final state. -/
def peak : List Move → WordState → ℕ
  | [], s => total s
  | m :: ms, s => max (total s) (peak ms (wordStep m s))

def Witness (C : ℕ) (s t : WordState) (ms : List Move) : Prop :=
  wordRun ms s = t ∧ peak ms s ≤ C

theorem source_le_peak (ms : List Move) (s : WordState) : total s ≤ peak ms s := by
  cases ms with
  | nil => exact le_rfl
  | cons m ms => exact le_max_left _ _

theorem end_le_peak (ms : List Move) (s : WordState) :
    total (wordRun ms s) ≤ peak ms s := by
  induction ms generalizing s with
  | nil => exact le_rfl
  | cons m ms ih => exact le_trans (ih (wordStep m s)) (le_max_right _ _)

theorem run_append (xs ys : List Move) (s : WordState) :
    wordRun (xs ++ ys) s = wordRun ys (wordRun xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons m ms ih => exact ih (wordStep m s)

theorem peak_append (xs ys : List Move) (s : WordState) :
    peak (xs ++ ys) s = max (peak xs s) (peak ys (wordRun xs s)) := by
  induction xs generalizing s with
  | nil => exact (max_eq_right (source_le_peak ys s)).symm
  | cons m ms ih =>
    simp only [List.cons_append, peak, wordRun, ih, max_assoc]

theorem witness_append {C : ℕ} {s t u : WordState} {xs ys : List Move}
    (hp : Witness C s t xs) (hq : Witness C t u ys) : Witness C s u (xs ++ ys) := by
  rcases hp with ⟨he, hb⟩
  rcases hq with ⟨hf, hc⟩
  constructor
  · simpa only [run_append, he] using hf
  · rw [peak_append, he]
    exact max_le hb hc

end Candidate.AK3Peak
