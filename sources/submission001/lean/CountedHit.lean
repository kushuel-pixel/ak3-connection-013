import Entry.ClassHit
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

namespace Independent.CountedHit
open Verify Verify.AtomicSemantics Verify.OneRelatorEntry
open Verify.AK3Mod5FixedPointAdapter (originalStart)
open Verify.AK3D3HRowConnection (D3)
open Verify.ROperationConnection (initial)

def xCount : Word → ℕ
  | [] => 0
  | l :: w => (if l.1 = 0 then 1 else 0) + xCount w

def coreCount (g : F) : ℕ := xCount (FreeGroup.reduceCyclically g.toWord)

private def sign (s : Bool) : ℤ := if s then 1 else -1

private theorem yLetter (s : Bool) :
    FreeGroup.mk ([(1,s)] : Word) = y ^ sign s := by
  cases s
  · change y⁻¹ = y ^ (-1 : ℤ)
    simp
  · change y = y ^ (1 : ℤ)
    simp

private theorem onlyY (w : Word) (h : xCount w = 0) :
    ∃ j : ℤ, FreeGroup.mk w = y ^ j := by
  induction w with
  | nil => exact ⟨0, (zpow_zero y).symm⟩
  | cons l t ih =>
    rcases l with ⟨g,s⟩
    rcases (show g = 0 ∨ g = 1 by omega) with rfl | rfl
    · simp [xCount] at h
    · have ht : xCount t = 0 := by simpa [xCount] using h
      obtain ⟨j,hj⟩ := ih ht
      refine ⟨sign s + j, ?_⟩
      change FreeGroup.mk ([(1,s)] : Word) * FreeGroup.mk t = _
      rw [yLetter,hj,zpow_add]

private theorem oneX (w : Word) (h : xCount w = 1) :
    ∃ (i j : ℤ) (neg : Bool),
      FreeGroup.mk w = y^i * (if neg then x⁻¹ else x) * y^j := by
  induction w with
  | nil => simp [xCount] at h
  | cons l t ih =>
    rcases l with ⟨g,s⟩
    rcases (show g = 0 ∨ g = 1 by omega) with rfl | rfl
    · have ht : xCount t = 0 := by simp [xCount] at h; omega
      obtain ⟨j,hj⟩ := onlyY t ht
      refine ⟨0,j,!s,?_⟩
      change FreeGroup.mk ([(0,s)] : Word) * FreeGroup.mk t = _
      rw [hj,zpow_zero,one_mul]
      cases s <;> rfl
    · have ht : xCount t = 1 := by simpa [xCount] using h
      obtain ⟨i,j,n,e⟩ := ih ht
      refine ⟨sign s + i,j,n,?_⟩
      change FreeGroup.mk ([(1,s)] : Word) * FreeGroup.mk t = _
      rw [yLetter,e,zpow_add]
      simp only [mul_assoc]

private theorem wordClass (w : Word) (h : xCount w = 1) :
    ∃ (k : ℤ) (c : F) (neg : Bool),
      FreeGroup.mk w = c*(if neg then (second k)⁻¹ else second k)*c⁻¹ := by
  obtain ⟨i,j,n,e⟩ := oneX w h
  cases n
  · refine ⟨-(j+i),y^i,false,?_⟩
    simp [e, second, zpow_add, mul_assoc]
  · refine ⟨i+j,(y^j)⁻¹,true,?_⟩
    rw [add_comm i j]
    simp [e, second, zpow_add, mul_assoc]

theorem class_of_count (g : F) (h : coreCount g = 1) :
    ∃ (k : ℤ) (c : F) (neg : Bool),
      g = c*(if neg then (second k)⁻¹ else second k)*c⁻¹ := by
  obtain ⟨k,c,n,hc⟩ := wordClass _ h
  let d := FreeGroup.mk (FreeGroup.reduceCyclically.conjugator g.toWord)
  have hd := congrArg FreeGroup.mk
    (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically g.toWord)
  change d * FreeGroup.mk (FreeGroup.reduceCyclically g.toWord) * d⁻¹ = FreeGroup.mk g.toWord at hd
  rw [FreeGroup.mk_toWord, hc] at hd
  refine ⟨k,d*c,n,?_⟩
  simpa only [mul_inv_rev,mul_assoc] using hd.symm

theorem hit_to_member (pre : List Move) (m : ℕ)
    (h : coreCount (groupRun pre originalStart).2 = 1) :
    ∃ tail : List Move, groupRun (pre++tail) originalStart = initial m := by
  obtain ⟨k,c,n,e⟩ := class_of_count _ h
  exact class_hit_to_member pre k c n m e

theorem d3_iff_count :
    (∃ p : List Move, groupRun p originalStart = D3) ↔
    ∃ p : List Move, coreCount (groupRun p originalStart).2 = 1 := by
  constructor
  · rintro ⟨p,e⟩
    refine ⟨p,?_⟩
    rw [e]
    decide +kernel
  · rintro ⟨p,h⟩
    obtain ⟨tail,e⟩ := hit_to_member p 3 h
    exact ⟨p++tail,e⟩

#print axioms class_of_count
#print axioms hit_to_member
#print axioms d3_iff_count
end Independent.CountedHit
