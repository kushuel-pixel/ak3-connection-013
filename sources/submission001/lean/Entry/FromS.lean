import Entry.FamilyGate
import Verify.AK3Mod5FixedPointAdapter
import Mathlib.Tactic.Ring

namespace Verify.OneRelatorEntry
open AtomicSemantics ResearchWords ROperationConnection
open AK3Mod5FixedPointAdapter (originalStart)

private def exponentHom (i : Fin 2) : F →* Multiplicative ℤ :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (if j = i then (1:ℤ) else 0)

def exponent (i : Fin 2) (a : F) : ℤ := (exponentHom i a).toAdd

@[simp] private theorem exp_one (i : Fin 2) : exponent i 1 = 0 := by
  simp [exponent]
@[simp] private theorem exp_mul (i : Fin 2) (a b : F) :
    exponent i (a*b) = exponent i a + exponent i b := by simp [exponent]
@[simp] private theorem exp_inv (i : Fin 2) (a : F) : exponent i a⁻¹ = -exponent i a := by
  simp [exponent]
@[simp] private theorem exp_pow (i : Fin 2) (a : F) (n : ℕ) :
    exponent i (a^n) = (n:ℤ)*exponent i a := by
  simp [exponent]
@[simp] private theorem exp_x (i : Fin 2) : exponent i x = if (0:Fin 2) = i then 1 else 0 := by
  simp [exponent,exponentHom,x]
@[simp] private theorem exp_y (i : Fin 2) : exponent i y = if (1:Fin 2) = i then 1 else 0 := by
  simp [exponent,exponentHom,y]

def det (s : GroupState) : ℤ :=
  exponent 0 s.1 * exponent 1 s.2 - exponent 1 s.1 * exponent 0 s.2

private theorem det_step (m : AtomicSemantics.Move) (s : GroupState) :
    det (groupStep m s) = if m = .m0 ∨ m = .m1 then -det s else det s := by
  rcases s with ⟨a,b⟩
  cases m <;> simp [groupStep,det,X,Y] <;> ring

private theorem unit_run (ms : List AtomicSemantics.Move) (s : GroupState)
    (unit : det s = 1 ∨ det s = -1) :
    det (groupRun ms s) = 1 ∨ det (groupRun ms s) = -1 := by
  induction ms generalizing s with
  | nil => exact unit
  | cons m rest ih =>
    apply ih
    rw [det_step]
    split <;> rcases unit with h|h <;> simp [h]

theorem project_as_power (n : ℤ) (a : F) :
    project n a = y ^ ((n:ℤ)*exponent 0 a + exponent 1 a) := by
  induction a using FreeGroup.induction_on with
  | one => simp
  | of i =>
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · change project n x = _
      change project n x = y ^ ((n:ℤ)*exponent 0 x + exponent 1 x)
      simp [project]
    · change project n y = y ^ ((n:ℤ)*exponent 0 y + exponent 1 y)
      simp [project]
  | inv_of i ih =>
    rw [map_inv,ih,← zpow_neg,exp_inv,exp_inv]
    congr 1
    ring
  | mul a b ha hb =>
    rw [map_mul,ha,hb,← zpow_add,exp_mul,exp_mul]
    congr 1
    ring

private theorem exp_zpow (i : Fin 2) (a : F) (k : ℤ) :
    exponent i (a^k) = k * exponent i a := by
  cases k with
  | ofNat d => simp
  | negSucc d =>
    change exponent i (a ^ (Int.negSucc d)) = (-((d:ℤ)+1)) * exponent i a
    simp [zpow_negSucc]
    ring

def flipSign (k : ℤ) (a : F) : Bool := decide (k*exponent 0 a + exponent 1 a = 1)

theorem project_after_hit (pre : List AtomicSemantics.Move) (k : ℤ)
    (hits : (groupRun pre originalStart).2 = second k) :
    project k (groupRun pre originalStart).1 = if flipSign k (groupRun pre originalStart).1 then y else Y := by
  let a := (groupRun pre originalStart).1
  have pair : groupRun pre originalStart = (a,second k) := Prod.ext rfl hits
  have d : det (a,second k) = -(k*exponent 0 a + exponent 1 a) := by
    simp [det,second,exp_zpow]
    ring
  have unit := unit_run pre originalStart (Or.inl (by decide +kernel))
  rw [pair,d] at unit
  change project k a = _
  rw [project_as_power]
  change y^(k*exponent 0 a+exponent 1 a) = if flipSign k a then y else Y
  rcases unit with low | high
  · have h : k*exponent 0 a + exponent 1 a = -1 := by omega
    simp [flipSign,h,Y]
  · have h : k*exponent 0 a + exponent 1 a = 1 := by omega
    simp [flipSign,h]

/-- For a nonnegative index, a second-only hit gives a path into the adjacent family. -/
theorem second_hit (pre : List AtomicSemantics.Move) (n : ℕ)
    (hits : (groupRun pre originalStart).2 = vFamily n) :
    groupRun (pre ++ enter n (groupRun pre originalStart).1 (flipSign n (groupRun pre originalStart).1))
      originalStart = initial n := by
  have ht := project_after_hit pre n (hits.trans (second_nat n).symm)
  rw [SevenPrefixUpperBound.groupRun_append]
  generalize ha : groupRun pre originalStart = s at *
  rcases s with ⟨a,b⟩
  change b = vFamily n at hits
  subst b
  exact enter_works n a _ ht

end Verify.OneRelatorEntry
