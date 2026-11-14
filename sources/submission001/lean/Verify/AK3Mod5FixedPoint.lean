import Verify.PermutationFixedPointNielsen
import Mathlib.Tactic.IntervalCases

/-! A concrete small consumer of the reusable fixed-point transport component.
The row whitelist is an explicit premise interface, not a classification of all
original-F paths. The prior mathematical argument supplies those row restrictions.
-/
namespace Verify.AK3Mod5FixedPoint
open Verify.PermutationFixedPointNielsen

abbrev Point := Fin 5

def x5 : Equiv.Perm Point where
  toFun i := ⟨(2*i.val)%5, Nat.mod_lt _ (by decide)⟩
  invFun i := ⟨(3*i.val)%5, Nat.mod_lt _ (by decide)⟩
  left_inv := by
    intro i; apply Fin.ext
    exact (by decide : ∀ j : Point, (3*((2*j.val)%5))%5 = j.val) i
  right_inv := by
    intro i; apply Fin.ext
    exact (by decide : ∀ j : Point, (2*((3*j.val)%5))%5 = j.val) i

def y5 : Equiv.Perm Point where
  toFun i := ⟨(i.val+1)%5, Nat.mod_lt _ (by decide)⟩
  invFun i := ⟨(i.val+4)%5, Nat.mod_lt _ (by decide)⟩
  left_inv := by
    intro i; apply Fin.ext
    exact (by decide : ∀ j : Point, (((j.val+1)%5)+4)%5 = j.val) i
  right_inv := by
    intro i; apply Fin.ext
    exact (by decide : ∀ j : Point, (((j.val+4)%5)+1)%5 = j.val) i

def r5 : Equiv.Perm Point := x5⁻¹*y5^3*x5*(y5⁻¹)^4
def b5 : Equiv.Perm Point := x5^2*(y5⁻¹)^5*x5⁻¹*y5^5
def t5 (negative : Bool) : Equiv.Perm Point :=
  if negative then x5*y5^3 else x5*(y5⁻¹)^3
def start : Pair Point := (r5,b5)

theorem r5_eq_one : r5 = 1 := by
  apply Equiv.ext
  exact (by decide : ∀ p : Point, r5 p = (1 : Equiv.Perm Point) p)

theorem b5_eq_x5 : b5 = x5 := by
  apply Equiv.ext
  exact (by decide : ∀ p : Point, b5 p = x5 p)

theorem start_fixes : BothFix (0 : Point) start := by
  constructor <;> decide

def step14 (i : Fin 14) : Step Point :=
  match i.val with
  | 0 => .invU | 1 => .invV | 2 => .mulU | 3 => .mulUInv
  | 4 => .mulV | 5 => .mulVInv
  | 6 => .conjU x5 | 7 => .conjU x5⁻¹
  | 8 => .conjU y5 | 9 => .conjU y5⁻¹
  | 10 => .conjV x5 | 11 => .conjV x5⁻¹
  | 12 => .conjV y5 | _ => .conjV y5⁻¹

/-- All six Nielsen operations, plus x/X conjugation on either component. -/
def SafeId (i : Fin 14) : Prop := i.val ≤ 7 ∨ i.val = 10 ∨ i.val = 11

theorem safeId_allowed (i : Fin 14) (hi : SafeId i) : allowedAt (0 : Point) (step14 i) := by
  rcases i with ⟨i,hlt⟩
  interval_cases i <;> simp_all [SafeId, allowedAt, step14, x5, Equiv.Perm.inv_def]

def run14 (ms : List (Fin 14)) (s : Pair Point) : Pair Point := run (ms.map step14) s

theorem run14_fixes (ms : List (Fin 14)) (s : Pair Point)
    (hm : ∀ i ∈ ms, SafeId i) (hs : BothFix (0 : Point) s) :
    BothFix (0 : Point) (run14 ms s) := by
  apply run_fixes
  · intro a ha
    rcases List.mem_map.mp ha with ⟨i,hi,hEq⟩
    rw [← hEq]
    exact safeId_allowed i (hm i hi)
  · exact hs

structure Row where
  negative : Bool
  first : Fin 14
  second : Fin 14

/-- Exact chronological conjugation rows from the accepted clustered k=±3 restriction. -/
def row (i : Fin 16) : Row :=
  match i.val with
  | 0 => ⟨true,6,8⟩ | 1 => ⟨true,6,13⟩
  | 2 => ⟨true,9,7⟩ | 3 => ⟨true,9,10⟩
  | 4 => ⟨true,10,9⟩ | 5 => ⟨true,10,12⟩
  | 6 => ⟨true,13,6⟩ | 7 => ⟨true,13,11⟩
  | 8 => ⟨false,6,9⟩ | 9 => ⟨false,6,12⟩
  | 10 => ⟨false,8,7⟩ | 11 => ⟨false,8,10⟩
  | 12 => ⟨false,10,8⟩ | 13 => ⟨false,10,13⟩
  | 14 => ⟨false,12,6⟩ | _ => ⟨false,12,11⟩

def rowSecond (i : Fin 16) : Equiv.Perm Point :=
  let r := row i
  (act (step14 r.second) (act (step14 r.first) (1,t5 r.negative))).2

def signedRowSecond (i : Fin 16) (inverse : Bool) : Equiv.Perm Point :=
  if inverse then (rowSecond i)⁻¹ else rowSecond i

theorem all_rows_nonfix : ∀ (i : Fin 16) (inverse : Bool),
    signedRowSecond i inverse (0 : Point) ≠ 0 := by decide

theorem no_safe_boundary (ms : List (Fin 14)) (hm : ∀ i ∈ ms, SafeId i)
    (i : Fin 16) (inverse : Bool) (u : Equiv.Perm Point) :
    run14 ms start ≠ (u,signedRowSecond i inverse) := by
  intro h
  have hf := run14_fixes ms start hm start_fixes
  rw [h] at hf
  exact all_rows_nonfix i inverse hf.2

theorem unsafe_conjugation_counterexample :
    (y5*x5*y5⁻¹) (0 : Point) ≠ 0 := by decide

/-- The wrong-k row (negative target, conjugate v by y) fixes0: whitelist matters. -/
theorem omitted_row_counterexample :
    (act (step14 (12 : Fin 14)) (act (step14 (6 : Fin 14)) (1,t5 true))).2
      (0 : Point) = 0 := by decide

end Verify.AK3Mod5FixedPoint
