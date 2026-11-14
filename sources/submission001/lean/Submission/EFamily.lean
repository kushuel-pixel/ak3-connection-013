import Verify.SevenPrefix

/-! A variable-n positive certificate in the existing fourteen-move semantics.
The peak formula is deliberately not asserted by this module. -/
namespace Verify.Submission.EFamily
open AtomicSemantics ResearchWords
open SevenPrefixUpperBound (groupRun_append)

def second (n : ℕ) : F := x * x * Y ^ (n + 1) * X * y ^ (n + 1)
def initial (n : ℕ) : GroupState := (uFamily n, second n)
def central (n : ℕ) : F := Y * x * Y ^ (n + 1) * X * y ^ (n + 1)

theorem run_first_Y (k : ℕ) (r s : F) :
    groupRun (List.replicate k .m9) (r,s) = (Y ^ k * r * y ^ k,s) := by
  induction k generalizing r with
  | zero => simp [groupRun]
  | succ k ih =>
    simp [List.replicate_succ, groupRun, groupStep, ih, pow_succ, mul_assoc]
    exact (pow_succ' y k).symm.trans (pow_succ y k)

theorem run_second_Y (k : ℕ) (r s : F) :
    groupRun (List.replicate k .m13) (r,s) = (r,Y ^ k * s * y ^ k) := by
  induction k generalizing s with
  | zero => simp [groupRun]
  | succ k ih =>
    simp [List.replicate_succ, groupRun, groupStep, ih, pow_succ, mul_assoc]
    exact (pow_succ' y k).symm.trans (pow_succ y k)

theorem run_second_y (k : ℕ) (r s : F) :
    groupRun (List.replicate k .m12) (r,s) = (r,y ^ k * s * Y ^ k) := by
  induction k generalizing s with
  | zero => simp [groupRun]
  | succ k ih =>
    simp [List.replicate_succ, groupRun, groupStep, ih, pow_succ, mul_assoc]
    exact (pow_succ' Y k).symm.trans (pow_succ Y k)

def prefixMoves (n : ℕ) : List Move := [.m6] ++ List.replicate (n + 1) .m9
def suffix : List Move := [.m3,.m4,.m2,.m5,.m2,.m8]
def word (n : ℕ) : List Move :=
  prefixMoves n ++ [.m5] ++ List.replicate (n + 1) .m13 ++ [.m2] ++
  List.replicate (n + 1) .m12 ++ suffix

theorem prefix_run (n : ℕ) :
    groupRun (prefixMoves n) (initial n) = (central n,second n) := by
  simp [prefixMoves, groupRun, groupStep, run_first_Y,
    initial, uFamily, central, X, Y, pow_succ', mul_assoc]

theorem first_mix (n : ℕ) :
    groupStep .m5 (central n,second n) = (central n,x*y) := by
  apply Prod.ext <;> simp [groupStep, central, second, X, Y, mul_assoc]

theorem second_conjugations (n : ℕ) :
    groupRun (List.replicate (n+1) .m13) (central n,x*y) =
    (central n,Y^(n+1)*x*y^((n+1)+1)) := by
  simp [run_second_Y, pow_succ', mul_assoc]

theorem second_mix (n : ℕ) :
    groupStep .m2 (central n,Y^(n+1)*x*y^((n+1)+1)) =
    (Y*x*y,Y^(n+1)*x*y^((n+1)+1)) := by
  apply Prod.ext
  · change central n * (Y^(n+1)*x*y^((n+1)+1)) = Y*x*y
    rw [pow_succ y (n+1)]
    simp [central, X, Y, mul_assoc]
  · rfl

theorem restore_second (n : ℕ) :
    groupRun (List.replicate (n+1) .m12) (Y*x*y,Y^(n+1)*x*y^((n+1)+1)) =
    (Y*x*y,x*y) := by
  rw [run_second_y]
  apply Prod.ext
  · rfl
  · change y^(n+1) * (Y^(n+1)*x*y^((n+1)+1)) * Y^(n+1) = x*y
    rw [pow_succ' y (n+1)]
    simp [Y, mul_assoc]

theorem suffix_run : groupRun suffix (Y*x*y,x*y) = (x,y) := by
  simp [suffix, groupRun, groupStep, Y, mul_assoc]

theorem reaches (n : ℕ) : groupRun (word n) (initial n) = (x,y) := by
  simp only [word, groupRun_append, prefix_run, groupRun, first_mix,
    second_conjugations, second_mix, restore_second, suffix_run]

theorem word_length (n : ℕ) : (word n).length = 3*n+12 := by
  simp [word, prefixMoves, suffix]
  omega

def canonicalInitial (n : ℕ) : WordState :=
  ((uFamily n).toWord,(second n).toWord)

theorem canonical_reaches (n : ℕ) :
    wordRun (word n) (canonicalInitial n) =
    ([ReducedWords.xLetter],[ReducedWords.yLetter]) := by
  have hr : ReducedState (canonicalInitial n) :=
    ⟨FreeGroup.isReduced_toWord,FreeGroup.isReduced_toWord⟩
  rw [wordRun_canonical _ _ hr]
  have he : evalState (canonicalInitial n) = initial n := by
    simp only [canonicalInitial,evalState,initial,FreeGroup.mk_toWord]
  rw [he,reaches]
  rfl

theorem zero_initial : initial 0 = (Y,x*x*Y*X*y) := by
  simp [initial,second,uFamily,X,Y]

end Verify.Submission.EFamily
