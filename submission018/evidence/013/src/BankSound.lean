import BankEngine
import CompactSound

namespace Candidate.AK3Peak.FixedS.BankSound
open Verify.AtomicSemantics
open AK3Compact (Ban Key encode)
open AK3Bank (Store has put readSlot addr every empty)

private theorem read_set (a : Array Nat) (i j k : Nat) (hi : i < a.size) :
    readSlot (a.set i k) j = if j = i then k else readSlot a j := by
  by_cases h : j = i
  · subst j; simp [readSlot, hi]
  · simp [readSlot, h, Ne.symm h]

private theorem has_empty (ns : List Nat) (k : Nat) : has (empty ns) k = false := by
  induction ns with
  | nil => simp [has, empty]
  | cons n ns ih =>
    simp only [empty, has, ih, Bool.or_false]
    by_cases h : addr n n k < n <;> simp [readSlot, h] <;> tauto

theorem has_put (t : Store) (k j : Nat) :
    has (put t k) j = true ↔ k = j ∨ has t j = true := by
  induction t with
  | last spill => simp [has,put,Std.HashSet.contains_insert]
  | row salt n cells rest ih =>
    simp only [put]
    by_cases hi : addr salt n k < cells.size
    · rw [dite_eq_left hi]
      by_cases hf : (k != 0 && cells[addr salt n k] == 0) = true
      · rw [ite_eq_left hf]
        have h0 : k ≠ 0 ∧ cells[addr salt n k] = 0 := by simpa using hf
        simp only [has,read_set]
        by_cases hj : j = k
        · subst j; simp [h0.1]
        · by_cases same : addr salt n j = addr salt n k
          · simp [same, Ne.symm hj, readSlot, hi, h0.2]
            grind
          · simp [same, Ne.symm hj]
      · rw [ite_eq_right hf]
        simp only [has, Bool.or_eq_true, ih]
        grind
    · rw [dite_eq_right hi]
      simp only [has, Bool.or_eq_true, ih]
      grind

theorem every_sound {p : Nat → Bool} {t : Store} (h : every p t = true)
    {j : Nat} (hm : has t j = true) : p j = true := by
  induction t with
  | last spill =>
    exact Std.HashSet.all_eq_true_iff_forall_mem.mp h j hm
  | row salt n cells rest ih =>
    simp only [every, Bool.and_eq_true, Array.all_eq_true] at h
    simp only [has, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hm
    rcases hm with ⟨hn,hslot⟩ | hr
    · unfold readSlot at hslot
      by_cases hi : addr salt n j < cells.size
      · have hv : cells[addr salt n j] = j := by simpa [hi] using hslot
        have hp := h.1 (addr salt n j) hi
        simpa [hv, hn] using hp
      · have he : (0 : Nat) = j := by simpa [hi] using hslot
        exact False.elim (hn he.symm)
    · exact ih h.2 hr

/-- The banked frontier is identical to the frontier in the proved hash-set search. -/
def Correspond (x : AK3Bank.Layer) (y : AK3Compact.Layer) : Prop :=
  x.front = y.front ∧ ∀ k, has x.seen k = true ↔ k ∈ y.seen

private theorem add_refines {x y} (h : Correspond x y) (j : Nat) :
    Correspond (AK3Bank.add x j) (AK3Compact.add y j) := by
  rcases h with ⟨hf,hm⟩
  by_cases hj : has x.seen j = true
  · simpa [AK3Bank.add,AK3Compact.add,hj,(hm j).mp hj,Correspond] using And.intro hf hm
  · have hn : j ∉ y.seen := fun h => hj ((hm j).mpr h)
    simp only [AK3Bank.add, AK3Compact.add, ite_eq_right hj, ite_eq_right hn, Correspond, hf, true_and]
    intro k
    simp [has_put, hm]

private theorem fold_refines {α : Type} (xs : List α)
    (f : AK3Bank.Layer → α → AK3Bank.Layer) (g : AK3Compact.Layer → α → AK3Compact.Layer)
    (step : ∀ x y a, Correspond x y → Correspond (f x a) (g y a))
    {x y} (h : Correspond x y) : Correspond (xs.foldl f x) (xs.foldl g y) := by
  induction xs generalizing x y with
  | nil => exact h
  | cons a xs ih => exact ih (step x y a h)

theorem ball_refines (ns : List Nat) (ban : Ban) (cap d : Nat) (s : WordState) :
    Correspond (AK3Bank.ball ns ban cap s d) (AK3Compact.ball ban cap s d) := by
  induction d with
  | zero =>
    constructor
    · rfl
    · intro k; simp [AK3Bank.ball, AK3Compact.ball, has_put, has_empty]
  | succ d ih =>
    let x := AK3Bank.ball ns ban cap s d
    let y := AK3Compact.ball ban cap s d
    change Correspond (x.front.foldl _ _) (y.front.foldl _ _)
    rw [show x.front = y.front from ih.1]
    apply fold_refines
    · intro a b k hab
      exact fold_refines _ _ _ (fun _ _ j hh => add_refines hh j) hab
    · exact ⟨rfl,ih.2⟩

theorem to_compact {ns : List Nat} {ban : Ban} {cap r t : Nat} {a b : WordState}
    (h : AK3Bank.separate ns ban cap r t a b = true) : AK3Compact.separate ban cap r t a b = true := by
  apply Std.HashSet.all_eq_true_iff_forall_mem.mpr
  intro k hk
  have hl := (ball_refines ns ban cap r a).2 k
  have hr := (ball_refines ns ban cap t b).2 k
  have hn := every_sound h (hl.mpr hk)
  simp only [Bool.not_eq_true'] at hn ⊢
  by_contra! hm
  have hb : has (AK3Bank.ball ns ban cap b t).seen k = true := hr.mpr (show (AK3Compact.ball ban cap b t).seen.contains k = true by cases he : (AK3Compact.ball ban cap b t).seen.contains k <;> simp_all)
  simp [hb] at hn

end Candidate.AK3Peak.FixedS.BankSound
