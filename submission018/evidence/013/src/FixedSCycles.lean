import FixedSPaths

namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics

def arm27 : List Move := [.m5,.m11,.m3,.m7,.m4]
def arm29 : List Move := [.m3,.m7,.m4,.m11,.m2]
def fork : WordState := (w! "xYXYxy", w! "xxxYYYY")
def joinState : WordState := (w! "YXYYxyyyyyX", w! "xxYYYYYXYxyyyyyX")

theorem arms_agree (s : WordState) (hs : ReducedState s) :
    wordRun arm27 s = wordRun arm29 s := by
  apply reduced_eq_of_eval (wordRun_reduced _ _ hs) (wordRun_reduced _ _ hs)
  rw [eval_wordRun, eval_wordRun]
  rcases evalState s with ⟨a,b⟩
  simp [arm27, arm29, groupRun, groupStep, Verify.X, mul_assoc]

def visited : List Move → WordState → List WordState
  | [], s => [s]
  | m :: ms, s => s :: visited ms (wordStep m s)

theorem both_branches :
    Witness 27 fork joinState arm27 ∧ Witness 29 fork joinState arm29 ∧
    (visited arm27 fork).map total = [13,19,17,24,22,27] ∧
    (visited arm29 fork).map total = [13,20,18,29,27,27] := by
  unfold Witness
  decide +kernel

def ten : List Move := arm27 ++ reverseMoves arm29
theorem simple_ten :
    ten.length = 10 ∧ Witness 29 fork fork ten ∧ (visited ten fork).dropLast.Nodup := by
  unfold Witness
  decide +kernel

def leftThree : List Move := [.m3,.m1,.m3]
def rightThree : List Move := [.m2,.m1,.m2]
def six := leftThree ++ reverseMoves rightThree

theorem low_excursions :
    Witness 28 lowP lowQ leftThree ∧ Witness 28 lowP lowQ rightThree ∧
    (visited leftThree lowP).map total = [21,28,28,21] ∧
    (visited rightThree lowP).map total = [21,28,28,21] ∧ Witness 21 lowP lowQ [.m1] := by
  unfold Witness
  decide +kernel

theorem simple_six :
    six.length = 6 ∧ Witness 28 lowP lowP six ∧ (visited six lowP).dropLast.Nodup := by
  unfold Witness
  decide +kernel

end Candidate.AK3Peak.FixedS
