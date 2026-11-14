import Adjacent.Family
import Verify.AK3D3BranchConnection

/-! The generator chooses point tests separating two small balls. Lean checks
every side against all 14 moves. No equality of stored Python sets is assumed. -/
namespace Verify.AdjacentDistance

open AtomicSemantics ResearchWords
open ROperationConnection (initial)
open PermutationFixedPointNielsen (Pair Step act)
open AK3D3BranchConnection (inverseMoves groupRun_inverse)
open SevenPrefixUpperBound (groupRun_append)

private abbrev Pt := Fin 6
private abbrev State := Pair Pt

private def points (a b c d e f : Pt) (i : Pt) : Pt :=
  match i.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f

private def permutation (f g : Pt → Pt) (l : ∀ i, g (f i) = i) (r : ∀ i, f (g i) = i) :
    Equiv.Perm Pt := ⟨f,g,l,r⟩

private def xp : Equiv.Perm Pt := permutation (points 5 1 3 0 2 4) (points 3 1 4 2 5 0) (by decide) (by decide)
private def yp : Equiv.Perm Pt := permutation (points 1 2 3 4 5 0) (points 5 0 1 2 3 4) (by decide) (by decide)

private def rep (k : Fin 6) : State :=
  match k.val with
  | 0 => (permutation (points 5 0 1 2 3 4) (points 1 2 3 4 5 0) (by decide) (by decide),
           permutation (points 5 1 3 0 2 4) (points 3 1 4 2 5 0) (by decide) (by decide))
  | 1 => (permutation (points 2 0 3 4 5 1) (points 1 5 0 2 3 4) (by decide) (by decide),
           permutation (points 4 5 1 3 0 2) (points 4 2 5 3 0 1) (by decide) (by decide))
  | 2 => (permutation (points 4 5 3 1 2 0) (points 5 3 4 2 0 1) (by decide) (by decide),
           permutation (points 2 4 5 1 3 0) (points 5 3 0 4 1 2) (by decide) (by decide))
  | 3 => (permutation (points 3 2 0 1 4 5) (points 2 3 1 0 4 5) (by decide) (by decide),
           permutation (points 0 2 4 5 1 3) (points 0 4 1 5 2 3) (by decide) (by decide))
  | 4 => (permutation (points 0 1 5 3 4 2) (points 0 1 5 3 4 2) (by decide) (by decide),
           permutation (points 3 0 2 4 5 1) (points 1 5 2 0 3 4) (by decide) (by decide))
  | _ => (permutation (points 5 3 4 0 1 2) (points 3 4 5 1 2 0) (by decide) (by decide),
           permutation (points 1 3 0 2 4 5) (points 2 0 3 1 4 5) (by decide) (by decide))


private def mark : F →* Equiv.Perm Pt :=
  FreeGroup.lift fun i : Fin 2 => if i = 0 then xp else yp

private theorem mark_x : mark x = xp := by
  change FreeGroup.lift _ (FreeGroup.of (0 : Fin 2)) = xp
  rw [FreeGroup.lift_apply_of]
  rfl

private theorem mark_y : mark y = yp := by
  change FreeGroup.lift _ (FreeGroup.of (1 : Fin 2)) = yp
  rw [FreeGroup.lift_apply_of]
  rfl

private def markPair (s : GroupState) : State := (mark s.1,mark s.2)

private def asStep : Move → Step Pt
  | .m0 => .invU | .m1 => .invV | .m2 => .mulU | .m3 => .mulUInv
  | .m4 => .mulV | .m5 => .mulVInv
  | .m6 => .conjU xp | .m7 => .conjU xp⁻¹ | .m8 => .conjU yp | .m9 => .conjU yp⁻¹
  | .m10 => .conjV xp | .m11 => .conjV xp⁻¹ | .m12 => .conjV yp | .m13 => .conjV yp⁻¹

private theorem mark_step (m : Move) (s : GroupState) :
    markPair (groupStep m s) = act (asStep m) (markPair s) := by
  rcases s with ⟨a,b⟩
  cases m <;> apply Prod.ext <;>
    simp only [markPair, groupStep, asStep, act, X, Y, map_mul, map_inv, mark_x, mark_y, inv_inv]

private def formula (k : ℕ) : State :=
  (xp⁻¹ * yp^k * xp * ((yp⁻¹)^k * yp⁻¹), xp * (yp⁻¹)^k)

private theorem mark_family (n : ℕ) : markPair (initial n) = rep ⟨n%6,by omega⟩ := by
  have period (a : Equiv.Perm Pt) (h : a^6 = 1) : a^n = a^(n%6) := by
    calc
      a^n = a^(n%6 + 6*(n/6)) := congrArg (fun k : ℕ => a^k) (Nat.mod_add_div n 6).symm
      _ = _ := by rw [pow_add, pow_mul, h, one_pow, mul_one]
  have hy : yp^6 = 1 := Equiv.ext (by decide +kernel : ∀ p : Pt, (yp^6) p = p)
  have hi : (yp⁻¹)^6 = 1 := Equiv.ext (by decide +kernel : ∀ p : Pt, ((yp⁻¹)^6) p = p)
  have first : ∀ (i : Fin 6) (p : Pt), (formula i.val).1 p = (rep i).1 p := by decide +kernel
  have second : ∀ (i : Fin 6) (p : Pt), (formula i.val).2 p = (rep i).2 p := by decide +kernel
  calc
    markPair (initial n) = formula (n%6) := by
      apply Prod.ext <;>
        simp only [markPair, initial, uFamily, vFamily, X,Y,map_mul,map_pow,map_inv,
          mark_x,mark_y, formula, pow_succ, period yp hy, period yp⁻¹ hi]
    _ = rep ⟨n%6,by omega⟩ :=
      Prod.ext (Equiv.ext (first ⟨n%6,by omega⟩)) (Equiv.ext (second ⟨n%6,by omega⟩))

private def moves : List Move :=
  [.m0,.m1,.m2,.m3,.m4,.m5,.m6,.m7,.m8,.m9,.m10,.m11,.m12,.m13]

private theorem all_ids (m : Move) : m ∈ moves := by cases m <;> decide

private def ball (p : State → Bool) : ℕ → State → Bool
  | 0,s => p s
  | k+1,s => p s && moves.all (fun m => ball p k (act (asStep m) s))

private theorem ball_sound (p : State → Bool) (k : ℕ) (s : GroupState) (ms : List Move)
    (ok : ball p k (markPair s) = true) (len : ms.length ≤ k) :
    p (markPair (groupRun ms s)) = true := by
  induction k generalizing s ms with
  | zero =>
    have hm : ms = [] := List.length_eq_zero_iff.mp (by omega)
    subst ms
    exact ok
  | succ k ih =>
    change (_ && _) = true at ok
    have h := Bool.and_eq_true_iff.mp ok
    cases ms with
    | nil => exact h.1
    | cons m rest =>
      apply ih (groupStep m s) rest
      · rw [mark_step]
        exact List.all_eq_true.mp h.2 m (all_ids m)
      · simpa using len

private theorem separate (p : State → Bool) (a b : GroupState) (d e : ℕ)
    (left : ball p d (markPair a) = true)
    (right : ball (fun s => !(p s)) e (markPair b) = true)
    (ms : List Move) (ends : groupRun ms a = b) : d+e < ms.length := by
  by_contra hn
  let u := ms.take d
  let v := ms.drop d
  have hsplit : u ++ v = ms := List.take_append_drop _ _
  have back : groupRun (inverseMoves v) b = groupRun u a := by
    rw [← ends, ← hsplit, groupRun_append, groupRun_inverse]
  have lu : u.length ≤ d := by simp [u]
  have lv : (inverseMoves v).length ≤ e := by simp [inverseMoves,v]; omega
  have yes := ball_sound p d a u left lu
  have no := ball_sound (fun s => !(p s)) e b (inverseMoves v) right lv
  rw [back] at no
  simp [yes] at no


private def cut0 (s : State) : Bool :=
  match (s.1 3).val with
  | 0 => match (s.2 1).val with
    | 0 => match (s.1 0).val with
      | 2 => false
      | _ => true
    | 2 => match (s.1 0).val with
      | 1 => false
      | 2 => false
      | _ => true
    | 4 => false
    | 5 => match (s.1 0).val with
      | 0 => true
      | 5 => true
      | _ => false
    | _ => true
  | 1 => match (s.2 0).val with
    | 4 => match (s.1 0).val with
      | 1 => true
      | 3 => match (s.1 1).val with
        | 2 => false
        | _ => true
      | _ => false
    | _ => true
  | 2 => match (s.1 0).val with
    | 1 => match (s.1 4).val with
      | 3 => false
      | 5 => false
      | _ => true
    | 2 => true
    | 3 => match (s.1 2).val with
      | 4 => match (s.1 1).val with
        | 0 => false
        | 1 => match (s.2 0).val with
          | 3 => false
          | _ => true
        | _ => true
      | 5 => false
      | _ => true
    | 5 => match (s.1 1).val with
      | 4 => false
      | _ => true
    | _ => false
  | 3 => match (s.2 0).val with
    | 1 => false
    | 3 => false
    | _ => true
  | 4 => match (s.1 0).val with
    | 0 => match (s.1 4).val with
      | 5 => false
      | _ => true
    | 1 => match (s.1 1).val with
      | 3 => false
      | _ => true
    | 3 => match (s.1 1).val with
      | 2 => false
      | _ => true
    | 4 => true
    | _ => false
  | 5 => match (s.2 3).val with
    | 1 => match (s.1 0).val with
      | 1 => false
      | 2 => false
      | _ => true
    | 3 => false
    | _ => true
  | _ => false

private theorem left0 : ball cut0 2 (rep 0) = true := by decide +kernel
private theorem right0 : ball (fun s => !(cut0 s)) 2 (rep 1) = true := by decide +kernel

private def cut1 (s : State) : Bool :=
  match (s.1 3).val with
  | 0 => match (s.1 4).val with
    | 1 => match (s.1 5).val with
      | 0 => true
      | 1 => true
      | 3 => match (s.2 0).val with
        | 2 => false
        | _ => true
      | 4 => match (s.1 2).val with
        | 3 => false
        | _ => true
      | _ => false
    | 2 => match (s.2 0).val with
      | 2 => false
      | 3 => false
      | _ => true
    | 3 => match (s.1 0).val with
      | 0 => true
      | 2 => match (s.1 2).val with
        | 1 => false
        | 4 => false
        | _ => true
      | 3 => true
      | _ => false
    | 4 => match (s.2 0).val with
      | 0 => true
      | 5 => true
      | _ => false
    | 5 => match (s.2 3).val with
      | 3 => match (s.1 1).val with
        | 4 => false
        | _ => true
      | _ => false
    | _ => true
  | 1 => match (s.2 0).val with
    | 4 => match (s.1 0).val with
      | 2 => match (s.1 4).val with
        | 3 => false
        | 4 => false
        | _ => true
      | 4 => match (s.1 1).val with
        | 2 => false
        | 5 => false
        | _ => true
      | 5 => match (s.2 2).val with
        | 0 => false
        | 3 => false
        | _ => true
      | _ => true
    | _ => false
  | 2 => match (s.2 3).val with
    | 0 => match (s.2 5).val with
      | 0 => true
      | 5 => match (s.1 0).val with
        | 5 => false
        | _ => true
      | _ => false
    | 1 => match (s.1 2).val with
      | 0 => match (s.2 0).val with
        | 2 => false
        | _ => true
      | 2 => true
      | _ => false
    | 2 => match (s.2 4).val with
      | 2 => true
      | 4 => match (s.1 1).val with
        | 4 => false
        | _ => true
      | _ => false
    | 3 => match (s.1 0).val with
      | 0 => false
      | 5 => match (s.1 2).val with
        | 0 => false
        | 4 => false
        | _ => true
      | _ => true
    | 5 => match (s.1 0).val with
      | 1 => match (s.1 1).val with
        | 0 => false
        | 4 => false
        | _ => true
      | 2 => true
      | _ => false
    | _ => false
  | 3 => match (s.2 4).val with
    | 2 => match (s.2 1).val with
      | 2 => true
      | 4 => true
      | _ => false
    | 4 => match (s.1 0).val with
      | 2 => false
      | _ => true
    | _ => false
  | 4 => match (s.1 2).val with
    | 0 => match (s.1 1).val with
      | 0 => true
      | 1 => match (s.1 4).val with
        | 3 => false
        | _ => true
      | 4 => true
      | 5 => match (s.1 4).val with
        | 1 => match (s.1 0).val with
          | 3 => false
          | _ => true
        | 2 => false
        | 3 => false
        | _ => true
      | _ => false
    | 1 => match (s.1 5).val with
      | 0 => match (s.1 1).val with
        | 2 => false
        | 3 => match (s.2 5).val with
          | 0 => match (s.2 1).val with
            | 4 => false
            | _ => true
          | _ => true
        | 5 => false
        | _ => true
      | 2 => match (s.1 0).val with
        | 0 => match (s.2 0).val with
          | 3 => false
          | _ => true
        | 3 => false
        | 5 => false
        | _ => true
      | 5 => false
      | _ => true
    | 2 => match (s.2 0).val with
      | 0 => true
      | 4 => true
      | _ => false
    | 3 => match (s.1 5).val with
      | 0 => false
      | 2 => false
      | 5 => match (s.2 0).val with
        | 0 => true
        | 4 => true
        | 5 => true
        | _ => false
      | _ => true
    | 5 => match (s.1 0).val with
      | 1 => match (s.2 0).val with
        | 2 => match (s.2 2).val with
          | 5 => false
          | _ => true
        | _ => true
      | 3 => match (s.2 0).val with
        | 4 => match (s.2 1).val with
          | 3 => false
          | _ => true
        | _ => false
      | 4 => true
      | 5 => true
      | _ => false
    | _ => true
  | 5 => match (s.2 3).val with
    | 1 => match (s.1 1).val with
      | 4 => match (s.1 2).val with
        | 1 => match (s.1 4).val with
          | 3 => false
          | _ => true
        | 2 => false
        | 3 => false
        | _ => true
      | 5 => true
      | _ => false
    | 3 => match (s.2 2).val with
      | 1 => match (s.2 1).val with
        | 0 => false
        | 2 => false
        | _ => true
      | 3 => true
      | _ => false
    | _ => false
  | _ => false

private theorem left1 : ball cut1 2 (rep 1) = true := by decide +kernel
private theorem right1 : ball (fun s => !(cut1 s)) 3 (rep 2) = true := by decide +kernel

private def cut2 (s : State) : Bool :=
  match (s.1 4).val with
  | 0 => match (s.2 2).val with
    | 0 => match (s.1 0).val with
      | 0 => true
      | 1 => match (s.2 0).val with
        | 2 => false
        | 5 => false
        | _ => true
      | 5 => match (s.1 3).val with
        | 1 => false
        | 4 => false
        | _ => true
      | _ => false
    | 1 => match (s.2 3).val with
      | 1 => true
      | 4 => match (s.1 0).val with
        | 3 => false
        | _ => true
      | _ => false
    | 3 => match (s.2 4).val with
      | 2 => match (s.1 2).val with
        | 1 => false
        | _ => true
      | 3 => true
      | _ => false
    | 5 => match (s.2 1).val with
      | 0 => false
      | 1 => false
      | 3 => match (s.2 0).val with
        | 2 => false
        | _ => true
      | _ => true
    | _ => false
  | 1 => match (s.1 0).val with
    | 0 => match (s.2 5).val with
      | 0 => true
      | _ => false
    | 1 => true
    | 2 => match (s.1 1).val with
      | 1 => true
      | 2 => true
      | 3 => match (s.1 3).val with
        | 0 => false
        | 5 => false
        | _ => true
      | _ => false
    | 3 => match (s.1 5).val with
      | 0 => match (s.1 1).val with
        | 5 => false
        | _ => true
      | 2 => match (s.1 2).val with
        | 0 => false
        | 4 => false
        | _ => true
      | 5 => false
      | _ => true
    | 5 => match (s.2 0).val with
      | 2 => true
      | 3 => true
      | _ => false
    | _ => false
  | 2 => match (s.1 5).val with
    | 0 => match (s.1 2).val with
      | 1 => match (s.2 2).val with
        | 0 => false
        | 4 => false
        | _ => true
      | 3 => match (s.1 0).val with
        | 1 => false
        | 4 => match (s.2 3).val with
          | 3 => match (s.2 4).val with
            | 1 => false
            | _ => true
          | _ => true
        | _ => true
      | 4 => match (s.2 0).val with
        | 0 => false
        | 1 => false
        | _ => true
      | 5 => false
      | _ => true
    | 2 => true
    | 3 => match (s.1 2).val with
      | 0 => match (s.2 2).val with
        | 0 => match (s.1 0).val with
          | 5 => false
          | _ => true
        | 4 => false
        | _ => true
      | 2 => true
      | 3 => true
      | _ => false
    | 4 => match (s.1 1).val with
      | 0 => match (s.1 0).val with
        | 1 => false
        | 5 => false
        | _ => true
      | 1 => match (s.1 0).val with
        | 5 => false
        | _ => true
      | 2 => true
      | 4 => true
      | _ => false
    | 5 => match (s.1 2).val with
      | 1 => match (s.2 2).val with
        | 0 => false
        | 4 => false
        | _ => true
      | 2 => true
      | 5 => true
      | _ => false
    | _ => false
  | 3 => match (s.2 5).val with
    | 0 => match (s.2 4).val with
      | 0 => true
      | 2 => true
      | 3 => match (s.1 0).val with
        | 0 => false
        | _ => true
      | _ => false
    | 4 => match (s.1 3).val with
      | 0 => true
      | 3 => true
      | 4 => true
      | _ => false
    | _ => false
  | 4 => match (s.1 5).val with
    | 1 => match (s.2 4).val with
      | 3 => true
      | _ => false
    | 3 => match (s.2 3).val with
      | 1 => match (s.1 0).val with
        | 0 => false
        | _ => true
      | 4 => match (s.1 1).val with
        | 5 => false
        | _ => true
      | _ => false
    | 4 => true
    | _ => false
  | 5 => match (s.2 3).val with
    | 0 => match (s.2 2).val with
      | 1 => match (s.1 1).val with
        | 1 => true
        | 2 => true
        | 5 => true
        | _ => false
      | 2 => false
      | 4 => match (s.2 0).val with
        | 1 => false
        | _ => true
      | _ => true
    | 1 => match (s.2 1).val with
      | 2 => false
      | 3 => false
      | _ => true
    | 2 => match (s.2 4).val with
      | 0 => match (s.1 1).val with
        | 2 => true
        | 4 => true
        | 5 => true
        | _ => false
      | 2 => true
      | 4 => true
      | 5 => match (s.2 0).val with
        | 0 => false
        | _ => true
      | _ => false
    | 4 => match (s.2 5).val with
      | 1 => match (s.1 0).val with
        | 0 => false
        | 1 => false
        | _ => true
      | 2 => true
      | 3 => match (s.1 2).val with
        | 1 => false
        | _ => true
      | 4 => true
      | _ => false
    | 5 => match (s.2 2).val with
      | 0 => match (s.1 0).val with
        | 0 => false
        | 2 => false
        | _ => true
      | 2 => true
      | 3 => match (s.2 0).val with
        | 4 => false
        | _ => true
      | 5 => true
      | _ => false
    | _ => false
  | _ => false

private theorem left2 : ball cut2 2 (rep 2) = true := by decide +kernel
private theorem right2 : ball (fun s => !(cut2 s)) 3 (rep 3) = true := by decide +kernel

private def cut3 (s : State) : Bool :=
  match (s.2 5).val with
  | 0 => match (s.1 3).val with
    | 1 => match (s.2 3).val with
      | 0 => true
      | 1 => match (s.1 0).val with
        | 5 => false
        | _ => true
      | 4 => true
      | 5 => match (s.1 0).val with
        | 2 => false
        | 5 => false
        | _ => true
      | _ => false
    | 5 => match (s.1 0).val with
      | 1 => match (s.2 1).val with
        | 3 => false
        | 4 => false
        | 5 => match (s.1 1).val with
          | 0 => false
          | _ => true
        | _ => true
      | 5 => true
      | _ => false
    | _ => false
  | 1 => match (s.2 0).val with
    | 0 => match (s.1 0).val with
      | 0 => false
      | _ => true
    | 1 => true
    | 2 => match (s.1 3).val with
      | 0 => match (s.1 0).val with
        | 3 => false
        | _ => true
      | 3 => match (s.1 0).val with
        | 1 => true
        | 3 => true
        | _ => false
      | 4 => false
      | _ => true
    | 3 => match (s.1 2).val with
      | 0 => match (s.1 3).val with
        | 0 => true
        | 1 => true
        | _ => false
      | _ => false
    | 5 => match (s.1 3).val with
      | 1 => true
      | 2 => true
      | _ => false
    | _ => false
  | 2 => match (s.2 0).val with
    | 2 => true
    | 3 => match (s.2 4).val with
      | 0 => match (s.1 0).val with
        | 0 => false
        | 1 => false
        | _ => true
      | 2 => true
      | 3 => true
      | 4 => match (s.1 0).val with
        | 0 => false
        | _ => true
      | _ => false
    | 4 => match (s.2 1).val with
      | 0 => match (s.1 2).val with
        | 2 => false
        | 5 => false
        | _ => true
      | 1 => match (s.1 1).val with
        | 1 => false
        | 4 => match (s.1 3).val with
          | 3 => false
          | _ => true
        | _ => true
      | 3 => false
      | _ => true
    | 5 => match (s.2 2).val with
      | 1 => match (s.1 0).val with
        | 4 => false
        | _ => true
      | 2 => true
      | 4 => match (s.1 0).val with
        | 0 => false
        | 1 => false
        | _ => true
      | 5 => true
      | _ => false
    | _ => false
  | 3 => match (s.2 4).val with
    | 0 => match (s.1 2).val with
      | 0 => true
      | 1 => true
      | 4 => true
      | _ => false
    | 1 => match (s.1 2).val with
      | 3 => match (s.1 5).val with
        | 4 => false
        | _ => true
      | 5 => match (s.2 0).val with
        | 0 => match (s.1 5).val with
          | 2 => false
          | _ => true
        | 1 => true
        | 3 => true
        | _ => false
      | _ => true
    | 2 => match (s.1 2).val with
      | 2 => match (s.2 0).val with
        | 4 => false
        | _ => true
      | 3 => match (s.1 0).val with
        | 2 => false
        | _ => true
      | 4 => match (s.1 1).val with
        | 1 => false
        | _ => true
      | 5 => false
      | _ => true
    | 4 => match (s.1 3).val with
      | 0 => true
      | 1 => true
      | 5 => true
      | _ => false
    | 5 => match (s.2 1).val with
      | 1 => match (s.1 0).val with
        | 3 => false
        | _ => true
      | 3 => true
      | 5 => true
      | _ => false
    | _ => true
  | 4 => match (s.1 2).val with
    | 0 => match (s.1 0).val with
      | 2 => false
      | 3 => match (s.1 1).val with
        | 1 => false
        | _ => true
      | 5 => false
      | _ => true
    | _ => false
  | 5 => match (s.1 2).val with
    | 0 => match (s.1 0).val with
      | 1 => match (s.1 1).val with
        | 3 => false
        | _ => true
      | 2 => false
      | 5 => false
      | _ => true
    | 1 => match (s.1 4).val with
      | 5 => false
      | _ => true
    | 2 => match (s.1 3).val with
      | 0 => match (s.1 0).val with
        | 1 => false
        | 3 => false
        | _ => true
      | 2 => true
      | 5 => match (s.2 1).val with
        | 1 => false
        | 2 => false
        | _ => true
      | _ => false
    | 3 => match (s.1 0).val with
      | 2 => false
      | 5 => false
      | _ => true
    | 4 => match (s.1 1).val with
      | 5 => false
      | _ => true
    | _ => false
  | _ => false

private theorem left3 : ball cut3 2 (rep 3) = true := by decide +kernel
private theorem right3 : ball (fun s => !(cut3 s)) 3 (rep 4) = true := by decide +kernel

private def cut4 (s : State) : Bool :=
  match (s.1 1).val with
  | 0 => match (s.1 4).val with
    | 0 => true
    | 2 => match (s.1 0).val with
      | 3 => match (s.2 2).val with
        | 0 => false
        | 4 => match (s.1 2).val with
          | 1 => false
          | _ => true
        | _ => true
      | 4 => false
      | 5 => false
      | _ => true
    | 4 => match (s.2 4).val with
      | 1 => true
      | 4 => match (s.1 5).val with
        | 1 => false
        | 2 => false
        | _ => true
      | _ => false
    | 5 => match (s.2 3).val with
      | 0 => true
      | 4 => true
      | _ => false
    | _ => false
  | 1 => match (s.1 4).val with
    | 0 => match (s.1 0).val with
      | 3 => false
      | 5 => false
      | _ => true
    | 1 => true
    | 3 => match (s.1 5).val with
      | 0 => match (s.2 0).val with
        | 0 => true
        | 4 => true
        | 5 => true
        | _ => false
      | 2 => false
      | 4 => false
      | _ => true
    | 4 => match (s.1 2).val with
      | 3 => match (s.1 0).val with
        | 2 => false
        | 5 => false
        | _ => true
      | _ => true
    | 5 => match (s.1 3).val with
      | 1 => true
      | 3 => true
      | 5 => true
      | _ => false
    | _ => false
  | 2 => match (s.1 4).val with
    | 1 => match (s.2 4).val with
      | 1 => match (s.1 0).val with
        | 3 => false
        | 4 => false
        | _ => true
      | 5 => match (s.2 0).val with
        | 0 => false
        | 4 => false
        | _ => true
      | _ => false
    | 2 => true
    | 3 => match (s.1 0).val with
      | 1 => match (s.2 5).val with
        | 0 => match (s.2 0).val with
          | 4 => false
          | _ => true
        | 1 => match (s.2 1).val with
          | 3 => false
          | 4 => false
          | _ => true
        | 2 => match (s.2 1).val with
          | 5 => false
          | _ => true
        | 4 => true
        | 5 => match (s.2 0).val with
          | 1 => false
          | 3 => false
          | _ => true
        | _ => false
      | 2 => true
      | 3 => true
      | _ => false
    | 4 => match (s.1 2).val with
      | 0 => false
      | 5 => false
      | _ => true
    | _ => false
  | 3 => match (s.1 3).val with
    | 2 => match (s.2 3).val with
      | 4 => match (s.1 5).val with
        | 1 => false
        | _ => true
      | _ => false
    | 3 => true
    | 4 => match (s.2 4).val with
      | 1 => true
      | 5 => true
      | _ => false
    | 5 => match (s.2 2).val with
      | 0 => false
      | 3 => false
      | _ => true
    | _ => false
  | 4 => match (s.2 3).val with
    | 0 => match (s.1 2).val with
      | 2 => match (s.1 3).val with
        | 5 => false
        | _ => true
      | 4 => true
      | _ => false
    | 2 => match (s.2 2).val with
      | 2 => true
      | 3 => true
      | 5 => match (s.1 2).val with
        | 1 => false
        | 5 => false
        | _ => true
      | _ => false
    | 3 => match (s.1 3).val with
      | 3 => match (s.1 4).val with
        | 0 => false
        | _ => true
      | 4 => true
      | _ => false
    | 4 => match (s.2 5).val with
      | 1 => match (s.1 3).val with
        | 5 => false
        | _ => true
      | 2 => match (s.1 3).val with
        | 1 => false
        | 5 => false
        | _ => true
      | 4 => true
      | _ => false
    | _ => false
  | 5 => match (s.2 4).val with
    | 5 => match (s.2 3).val with
      | 0 => true
      | 3 => match (s.1 0).val with
        | 1 => false
        | 4 => false
        | _ => true
      | 4 => match (s.1 2).val with
        | 2 => match (s.2 0).val with
          | 2 => false
          | _ => true
        | 3 => match (s.1 0).val with
          | 0 => false
          | _ => true
        | 4 => true
        | 5 => true
        | _ => false
      | 5 => true
      | _ => false
    | _ => false
  | _ => false

private theorem left4 : ball cut4 2 (rep 4) = true := by decide +kernel
private theorem right4 : ball (fun s => !(cut4 s)) 3 (rep 5) = true := by decide +kernel


private theorem transfer_cut (n : ℕ) (r t : Fin 6) (hr : n%6 = r.val)
    (ht : (n+1)%6 = t.val) (p : State → Bool) (e : ℕ)
    (l : ball p 2 (rep r) = true) (b : ball (fun s => !(p s)) e (rep t) = true)
    (ms : List Move) (ends : groupRun ms (initial n) = initial (n+1)) :
    2+e < ms.length := by
  have first : markPair (initial n) = rep r :=
    (mark_family n).trans (congrArg rep (Fin.ext hr))
  have last : markPair (initial (n+1)) = rep t :=
    (mark_family (n+1)).trans (congrArg rep (Fin.ext ht))
  exact separate p _ _ 2 e (by rwa [first]) (by rwa [last]) ms ends

/-- Any original, unrestricted path in the four residue classes costs at least six IDs. -/
theorem adjacent_lower (n : ℕ) (hr : n%6 = 1 ∨ n%6 = 2 ∨ n%6 = 3 ∨ n%6 = 4)
    (ms : List Move) (ends : groupRun ms (initial n) = initial (n+1)) :
    6 ≤ ms.length := by
  rcases hr with h | h | h | h
  · exact transfer_cut n 1 2 h (by change (n+1)%6 = 2; omega) cut1 3 left1 right1 ms ends
  · exact transfer_cut n 2 3 h (by change (n+1)%6 = 3; omega) cut2 3 left2 right2 ms ends
  · exact transfer_cut n 3 4 h (by change (n+1)%6 = 4; omega) cut3 3 left3 right3 ms ends
  · exact transfer_cut n 4 5 h (by change (n+1)%6 = 5; omega) cut4 3 left4 right4 ms ends

theorem adjacent_shortest_six (n : ℕ) (hr : n%6 = 1 ∨ n%6 = 2 ∨ n%6 = 3 ∨ n%6 = 4) :
    (∃ ms : List Move, ms.length = 6 ∧ groupRun ms (initial n) = initial (n+1)) ∧
    (∀ ms : List Move, groupRun ms (initial n) = initial (n+1) → 6 ≤ ms.length) :=
  ⟨⟨[.m11,.m4,.m3,.m9,.m2,.m8],rfl,AdjacentFamily.adjacent_via_first n⟩, adjacent_lower n hr⟩

theorem zero_shortest_five :
    (∃ ms : List Move, ms.length = 5 ∧ groupRun ms (initial 0) = initial 1) ∧
    (∀ ms : List Move, groupRun ms (initial 0) = initial 1 → 5 ≤ ms.length) := by
  constructor
  · exact ⟨[.m4,.m3,.m9,.m2,.m8], rfl, by decide +kernel⟩
  · exact transfer_cut 0 0 1 rfl rfl cut0 2 left0 right0

end Verify.AdjacentDistance
