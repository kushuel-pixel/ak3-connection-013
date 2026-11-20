import B5Bridge42
import B5BallEngine
import Std.Data.HashSet.Lemmas

namespace Candidate.AK3Peak.BallSearch
open Verify.AtomicSemantics
open Bridge42 (InBall)
open AK3BallEngine (digit letter pack unpack Key Table encode decode children Layer extend ball separate)

theorem digit_lt (a : Letter) : digit a < 4 := by
  rcases a with ⟨⟨_ | _ | n, hi⟩, b⟩ <;> first | omega | cases b <;> simp [digit]

theorem letter_digit (a : Letter) : letter (digit a) = a := by
  rcases a with ⟨⟨_ | _ | n, hi⟩, b⟩ <;> first | omega | cases b <;> rfl

theorem one_le_pack (w : Word) : 1 ≤ pack w := by
  induction w with
  | nil => decide
  | cons a w ih => simp only [pack]; omega

@[simp] theorem unpack_pack (w : Word) : unpack (pack w) = w := by
  induction w with
  | nil => rw [pack, unpack]; rfl
  | cons a w ih =>
    have hd := digit_lt a
    have hp := one_le_pack w
    rw [pack, unpack, dite_eq_right (by omega)]
    have hmod : (4 * pack w + digit a) % 4 = digit a := by omega
    have hdiv : (4 * pack w + digit a) / 4 = pack w := by omega
    rw [hmod, hdiv, letter_digit, ih]

@[simp] theorem decode_encode (s : WordState) : decode (encode s) = s := by
  simp [encode, decode]

private theorem reduce_eq (w : Word) : AK3BallEngine.reduce w = FreeGroup.reduce w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [AK3BallEngine.reduce, FreeGroup.reduce.cons, ih]
    cases FreeGroup.reduce w <;> rfl

private theorem inverse_eq (w : Word) : AK3BallEngine.inverse w = FreeGroup.invRev w := rfl

theorem step_eq (m : Move) (s : WordState) :
    AK3BallEngine.step (moveId m) s = wordStep m s := by
  rcases s with ⟨a,b⟩
  cases m <;> simp only [AK3BallEngine.step, moveId, wordStep, wordConj, AK3BallEngine.conj,
    reduce_eq, inverse_eq, AK3BallEngine.xLetter, AK3BallEngine.XLetter,
    AK3BallEngine.yLetter, AK3BallEngine.YLetter]

theorem mem_moveIds (m : Move) : moveId m ∈ AK3BallEngine.moveIds := by cases m <;> decide

theorem child_mem {cap : Nat} (s : WordState) (m : Move) (h : total (wordStep m s) ≤ cap) :
    encode (wordStep m s) ∈ children cap (encode s) := by
  apply List.mem_filterMap.mpr
  exact ⟨moveId m, mem_moveIds m, by
    simp only [decode_encode, step_eq]
    exact ite_eq_left h⟩

private theorem fold_hits (cap : Nat) (xs : List Key) (init : Table) (k : Key) :
    k ∈ xs.foldl (fun (acc : Table) j => acc.insertMany (children cap j)) init ↔
    k ∈ init ∨ ∃ j ∈ xs, k ∈ children cap j := by
  induction xs generalizing init with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.mem_insertMany_list, List.contains_iff_mem,
      List.mem_cons]
    grind

private theorem next_mem {cap : Nat} {b : Layer} {x y : Key} (hx : x ∈ b.front)
    (hy : y ∈ children cap x) : y ∈ (extend cap b).seen := by
  by_cases hs : y ∈ b.seen
  · exact Std.HashSet.mem_union_of_left hs
  · apply Std.HashSet.mem_union_of_right
    apply Std.HashSet.mem_diff_iff.mpr
    refine ⟨?_, hs⟩
    rw [Std.HashSet.fold_eq_foldl_toList, fold_hits]
    exact Or.inr ⟨x, Std.HashSet.mem_toList.mpr hx, hy⟩

def ClosedBehind (cap : Nat) (b : Layer) : Prop :=
  ∀ x ∈ b.seen, x ∉ b.front → ∀ y ∈ children cap x, y ∈ b.seen

private theorem closed (cap : Nat) (s : WordState) (n : Nat) : ClosedBehind cap (ball cap s n) := by
  induction n with
  | zero => intro x hx hn; exact (hn hx).elim
  | succ n ih =>
    let b := ball cap s n
    intro x hx hn y hy
    change x ∈ (extend cap b).seen at hx
    change x ∉ (extend cap b).front at hn
    have hold : x ∈ b.seen := (Std.HashSet.mem_union_iff.mp hx).resolve_right hn
    by_cases hf : x ∈ b.front
    · exact next_mem hf hy
    · exact Std.HashSet.mem_union_of_left (ih x hold hf y hy)

private theorem step_seen {cap : Nat} {s u : WordState} {n : Nat} (m : Move)
    (hu : encode u ∈ (ball cap s n).seen) (ht : total (wordStep m u) ≤ cap) :
    encode (wordStep m u) ∈ (ball cap s (n+1)).seen := by
  have h := child_mem u m ht
  by_cases hf : encode u ∈ (ball cap s n).front
  · exact next_mem hf h
  · exact Std.HashSet.mem_union_of_left (closed cap s n _ hu hf _ h)

theorem cover {cap n : Nat} {s u : WordState} (h : InBall cap n s u) :
    encode u ∈ (ball cap s n).seen := by
  obtain ⟨ms, hm, he, hp⟩ := h
  subst u
  induction n generalizing ms with
  | zero =>
    have hz : ms = [] := List.length_eq_zero_iff.mp (by omega)
    subst ms
    exact Std.HashSet.mem_insert_self
  | succ n ih =>
    cases hl : ms.getLast? with
    | none =>
      have hz : ms = [] := List.getLast?_eq_none_iff.mp hl
      subst ms
      exact Std.HashSet.mem_union_of_left (ih [] (by simp) hp)
    | some m =>
      obtain ⟨xs, rfl⟩ := List.getLast?_eq_some_iff.mp hl
      have hxs : xs.length ≤ n := by simpa using hm
      rw [peak_append] at hp
      rw [run_append]
      exact step_seen m (ih xs hxs (max_le_iff.mp hp).1)
        (le_trans (end_le_peak [m] (wordRun xs s)) (max_le_iff.mp hp).2)

theorem separate_sound {cap r t : Nat} {a b : WordState} (h : separate cap r t a b = true)
    (u : WordState) (ha : InBall cap r a u) (hb : InBall cap t b u) : False := by
  have hh := Std.HashSet.all_eq_true_iff_forall_mem.mp h (encode u) (cover ha)
  simp [show (ball cap b t).seen.contains (encode u) = true from cover hb] at hh

theorem shortest_of_check (h : separate 22 16 25 ak3 source = true) :
    (∃ ms : List Move, ms.length = 42 ∧ Witness 22 ak3 source ms) ∧
    (∀ ms : List Move, Witness 22 ak3 source ms → 42 ≤ ms.length) :=
  Bridge42.shortest_of_disjoint (separate_sound h)

end Candidate.AK3Peak.BallSearch

#print axioms Candidate.AK3Peak.BallSearch.cover
#print axioms Candidate.AK3Peak.BallSearch.separate_sound
#print axioms Candidate.AK3Peak.BallSearch.shortest_of_check
