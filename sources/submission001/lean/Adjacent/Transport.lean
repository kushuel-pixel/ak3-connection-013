import Adjacent.Family

/-! Explicit witnesses between family members and composition with the public n+8 exit. -/
namespace Verify.AdjacentFamily

open AtomicSemantics ROperationConnection
open SevenPrefixUpperBound (groupRun_append)

/-- Emit every primitive ID, including steps that happen to fix a state. -/
def betweenMoves (n m : ℕ) : List AtomicSemantics.Move :=
  if n ≤ m then
    (List.replicate (m-n) [.m11,.m4,.m3,.m9,.m2,.m8]).flatten
  else
    (List.replicate (n-m) [.m9,.m3,.m8,.m2,.m5,.m10]).flatten

theorem adjacent_back (n : ℕ) :
    groupRun [.m9,.m3,.m8,.m2,.m5,.m10] (initial (n+1)) = initial n := by
  rw [← adjacent_via_first n]
  generalize initial n = s
  rcases s with ⟨a,b⟩
  apply Prod.ext <;> simp [groupRun, groupStep, X, Y, mul_assoc]

private theorem up_iter (n k : ℕ) :
    groupRun ((List.replicate k [.m11,.m4,.m3,.m9,.m2,.m8]).flatten) (initial n)
      = initial (n+k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, groupRun_append, adjacent_via_first, ih]
    congr 1
    omega

private theorem down_iter (n k : ℕ) :
    groupRun ((List.replicate k [.m9,.m3,.m8,.m2,.m5,.m10]).flatten) (initial (n+k))
      = initial n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, groupRun_append]
    change groupRun _ (groupRun _ (initial ((n+k)+1))) = _
    rw [adjacent_back]
    exact ih

theorem between_run (n m : ℕ) :
    groupRun (betweenMoves n m) (initial n) = initial m := by
  by_cases h : n ≤ m
  · rw [betweenMoves, ite_eq_left h, up_iter]
    congr 1
    omega
  · rw [betweenMoves, ite_eq_right h]
    have e : m + (n-m) = n := by omega
    simpa only [e] using down_iter m (n-m)

theorem between_length (n m : ℕ) :
    (betweenMoves n m).length = 6 * ((m-n)+(n-m)) := by
  have lengths (k : ℕ) (xs : List AtomicSemantics.Move) :
      (List.replicate k xs).flatten.length = xs.length*k := by
    induction k with
    | zero => simp
    | succ k ih => simp [List.replicate_succ, ih, Nat.mul_succ, Nat.add_comm]
  by_cases h : n ≤ m
  · simp [betweenMoves, h, lengths, Nat.sub_eq_zero_of_le h]
  · have hm : m ≤ n := by omega
    simp [betweenMoves, h, lengths, Nat.sub_eq_zero_of_le hm]

/-- A prefix ending at any member gives two concrete continuations with exact costs. -/
theorem finish_from_member (s : GroupState) (pre : List AtomicSemantics.Move) (n m : ℕ)
    (hits : groupRun pre s = initial n) :
    (groupRun (pre ++ betweenMoves n m) s = initial m ∧
      (pre ++ betweenMoves n m).length = pre.length + 6*((m-n)+(n-m))) ∧
    (groupRun (pre ++ SevenPrefixUpperBound.word n) s = (x,y) ∧
      (pre ++ SevenPrefixUpperBound.word n).length = pre.length+(n+8)) := by
  simp only [groupRun_append, hits, between_run, between_length,
    SevenPrefixUpperBound.reaches, SevenPrefixUpperBound.word_length, List.length_append,
    and_self]

end Verify.AdjacentFamily
