import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

namespace Verify

/-- Free group on two generators `x = 0`, `y = 1`. -/
abbrev F := FreeGroup (Fin 2)

def x : F := FreeGroup.of 0
def y : F := FreeGroup.of 1
def X : F := x⁻¹
def Y : F := y⁻¹

end Verify

namespace Verify.ReducedWords

abbrev Letter := Fin 2 × Bool
abbrev xLetter : Letter := (0, true)
abbrev yLetter : Letter := (1, true)
abbrev XLetter : Letter := (0, false)
abbrev YLetter : Letter := (1, false)

end Verify.ReducedWords

namespace Verify.AtomicSemantics

abbrev Letter := ReducedWords.Letter
abbrev Word := List Letter
abbrev WordState := Word × Word
abbrev GroupState := Verify.F × Verify.F

inductive Move where
  | m0 | m1 | m2 | m3 | m4 | m5 | m6
  | m7 | m8 | m9 | m10 | m11 | m12 | m13
  deriving DecidableEq

def moveId : Move → ℕ
  | .m0 => 0 | .m1 => 1 | .m2 => 2 | .m3 => 3 | .m4 => 4 | .m5 => 5
  | .m6 => 6 | .m7 => 7 | .m8 => 8 | .m9 => 9 | .m10 => 10
  | .m11 => 11 | .m12 => 12 | .m13 => 13

def evalState (w : WordState) : GroupState :=
  (FreeGroup.mk w.1, FreeGroup.mk w.2)

def wordConj (a : Letter) (w : Word) : Word :=
  FreeGroup.reduce ([a] ++ w ++ FreeGroup.invRev [a])

def wordStep : Move → WordState → WordState
  | .m0, (r, s) => (FreeGroup.invRev r, s)
  | .m1, (r, s) => (r, FreeGroup.invRev s)
  | .m2, (r, s) => (FreeGroup.reduce (r ++ s), s)
  | .m3, (r, s) => (FreeGroup.reduce (r ++ FreeGroup.invRev s), s)
  | .m4, (r, s) => (r, FreeGroup.reduce (s ++ r))
  | .m5, (r, s) => (r, FreeGroup.reduce (s ++ FreeGroup.invRev r))
  | .m6, (r, s) => (wordConj ReducedWords.xLetter r, s)
  | .m7, (r, s) => (wordConj ReducedWords.XLetter r, s)
  | .m8, (r, s) => (wordConj ReducedWords.yLetter r, s)
  | .m9, (r, s) => (wordConj ReducedWords.YLetter r, s)
  | .m10, (r, s) => (r, wordConj ReducedWords.xLetter s)
  | .m11, (r, s) => (r, wordConj ReducedWords.XLetter s)
  | .m12, (r, s) => (r, wordConj ReducedWords.yLetter s)
  | .m13, (r, s) => (r, wordConj ReducedWords.YLetter s)

def groupStep : Move → GroupState → GroupState
  | .m0, (r, s) => (r⁻¹, s)
  | .m1, (r, s) => (r, s⁻¹)
  | .m2, (r, s) => (r * s, s)
  | .m3, (r, s) => (r * s⁻¹, s)
  | .m4, (r, s) => (r, s * r)
  | .m5, (r, s) => (r, s * r⁻¹)
  | .m6, (r, s) => (Verify.x * r * Verify.X, s)
  | .m7, (r, s) => (Verify.X * r * Verify.x, s)
  | .m8, (r, s) => (Verify.y * r * Verify.Y, s)
  | .m9, (r, s) => (Verify.Y * r * Verify.y, s)
  | .m10, (r, s) => (r, Verify.x * s * Verify.X)
  | .m11, (r, s) => (r, Verify.X * s * Verify.x)
  | .m12, (r, s) => (r, Verify.y * s * Verify.Y)
  | .m13, (r, s) => (r, Verify.Y * s * Verify.y)

def wordRun : List Move → WordState → WordState
  | [], w => w
  | m :: ms, w => wordRun ms (wordStep m w)

def groupRun : List Move → GroupState → GroupState
  | [], s => s
  | m :: ms, s => groupRun ms (groupStep m s)

def ReducedState (w : WordState) : Prop :=
  FreeGroup.IsReduced w.1 ∧ FreeGroup.IsReduced w.2

theorem mk_wordConj (a : Letter) (w : Word) :
    FreeGroup.mk (wordConj a w) =
      FreeGroup.mk [a] * FreeGroup.mk w * (FreeGroup.mk [a])⁻¹ := by
  simp only [wordConj, FreeGroup.reduce.self, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]

theorem eval_wordStep (m : Move) (w : WordState) :
    evalState (wordStep m w) = groupStep m (evalState w) := by
  have hx : FreeGroup.mk [ReducedWords.xLetter] = Verify.x := rfl
  have hX : FreeGroup.mk [ReducedWords.XLetter] = Verify.X := rfl
  have hy : FreeGroup.mk [ReducedWords.yLetter] = Verify.y := rfl
  have hY : FreeGroup.mk [ReducedWords.YLetter] = Verify.Y := rfl
  rcases w with ⟨r, s⟩
  cases m <;> apply Prod.ext <;>
    simp only [wordStep, groupStep, evalState, mk_wordConj, FreeGroup.reduce.self,
      ← FreeGroup.inv_mk, ← FreeGroup.mul_mk, hx, hX, hy, hY]
  all_goals simp [Verify.X, Verify.Y]

theorem wordStep_reduced (m : Move) (w : WordState) (hw : ReducedState w) :
    ReducedState (wordStep m w) := by
  rcases w with ⟨r, s⟩
  rcases hw with ⟨hr, hs⟩
  have hreduce (L : Word) : FreeGroup.IsReduced (FreeGroup.reduce L) :=
    FreeGroup.IsReduced.of_reduce_eq FreeGroup.reduce.idem
  have hinv (L : Word) (hL : FreeGroup.IsReduced L) :
      FreeGroup.IsReduced (FreeGroup.invRev L) :=
    FreeGroup.IsReduced.of_reduce_eq (by rw [FreeGroup.reduce_invRev, hL.reduce_eq])
  cases m <;> dsimp only [wordStep, wordConj, ReducedState] <;> constructor
  all_goals first
    | exact hr
    | exact hs
    | exact hinv r hr
    | exact hinv s hs
    | exact hreduce _

theorem eval_wordRun (moves : List Move) (w : WordState) :
    evalState (wordRun moves w) = groupRun moves (evalState w) := by
  induction moves generalizing w with
  | nil => rfl
  | cons m ms ih =>
    simpa only [wordRun, groupRun, eval_wordStep] using ih (wordStep m w)

theorem wordRun_reduced (moves : List Move) (w : WordState) (hw : ReducedState w) :
    ReducedState (wordRun moves w) := by
  induction moves generalizing w with
  | nil => exact hw
  | cons m ms ih => exact ih (wordStep m w) (wordStep_reduced m w hw)

theorem wordRun_canonical (moves : List Move) (w : WordState) (hw : ReducedState w) :
    wordRun moves w =
      (FreeGroup.toWord (groupRun moves (evalState w)).1,
       FreeGroup.toWord (groupRun moves (evalState w)).2) := by
  have hr := wordRun_reduced moves w hw
  have he := eval_wordRun moves w
  apply Prod.ext
  · have h := congrArg Prod.fst he
    change FreeGroup.mk (wordRun moves w).1 = (groupRun moves (evalState w)).1 at h
    rw [← h, FreeGroup.toWord_mk, hr.1.reduce_eq]
  · have h := congrArg Prod.snd he
    change FreeGroup.mk (wordRun moves w).2 = (groupRun moves (evalState w)).2 at h
    rw [← h, FreeGroup.toWord_mk, hr.2.reduce_eq]

end Verify.AtomicSemantics
