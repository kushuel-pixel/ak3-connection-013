import Entry.FromS
import Verify.AK3D3HRowConnection

namespace Verify.OneRelatorEntry
open AtomicSemantics ResearchWords ROperationConnection
open AK3Mod5FixedPointAdapter (originalStart originalR)
open AK3D3HRowConnection (D3)
open SevenPrefixUpperBound (groupRun_append)

private theorem up (k : ℤ) : groupStep .m4 (Y,second k) = (Y,second (k+1)) := by
  change (Y,second k*Y) = _
  rw [add_comm k 1]
  simp [second,Y,zpow_add,mul_assoc]

private theorem down (k : ℤ) : groupStep .m5 (Y,second k) = (Y,second (k-1)) := by
  change (Y,second k*Y⁻¹) = _
  rw [sub_eq_add_neg,add_comm k (-1)]
  simp [second,Y,zpow_add,mul_assoc]

private theorem many_up (d : ℕ) (k : ℤ) :
    groupRun (List.replicate d .m4) (Y,second k) = (Y,second (k+d)) := by
  induction d generalizing k with
  | zero => simp [groupRun]
  | succ d ih =>
    rw [List.replicate_succ]
    change groupRun _ (groupStep .m4 _) = _
    rw [up, ih]
    congr 2
    omega

private theorem many_down (d : ℕ) (k : ℤ) :
    groupRun (List.replicate d .m5) (Y,second k) = (Y,second (k-d)) := by
  induction d generalizing k with
  | zero => simp [groupRun]
  | succ d ih =>
    rw [List.replicate_succ]
    change groupRun _ (groupStep .m5 _) = _
    rw [down, ih]
    congr 2
    omega

def slide (d : ℤ) : List AtomicSemantics.Move :=
  match d with
  | .ofNat t => List.replicate t .m4
  | .negSucc t => List.replicate (t+1) .m5

theorem slide_run (k d : ℤ) :
    groupRun (slide d) (Y,second k) = (Y,second (k+d)) := by
  cases d with
  | ofNat t => exact many_up t k
  | negSucc t =>
    rw [slide,many_down]
    congr 2

private theorem projected_Y (k : ℤ) : project k Y = Y := by simp [project,Y]

/-- Go through first relator Y, reach any chosen nonnegative family index. -/
def viaY (k : ℤ) (m : ℕ) (a : F) (flip : Bool) : List AtomicSemantics.Move :=
  (if flip then [.m0] else []) ++ connector k (if flip then a⁻¹ else a) Y ++
  slide ((m:ℤ)-k) ++ connector m Y (uFamily m)

theorem viaY_works (k : ℤ) (m : ℕ) (a : F) (flip : Bool)
    (test : project k a = if flip then y else Y) :
    groupRun (viaY k m a flip) (a,second k) = initial m := by
  let b := if flip then a⁻¹ else a
  have start : groupRun (if flip then [.m0] else []) (a,second k) = (b,second k) := by
    cases flip <;> rfl
  have aligned : project k b = project k Y := by
    cases flip <;> simp_all [b,Y,project]
  have last : project m Y = project m (uFamily m) := (projected_Y m).trans (project_initial_first m).symm
  unfold viaY
  rw [groupRun_append,groupRun_append,groupRun_append,start,connector_works k b Y aligned,slide_run]
  have mid : k + ((m:ℤ)-k) = m := by omega
  rw [mid,connector_works _ _ _ last,second_nat]
  rfl

theorem signed_second_hit (pre : List AtomicSemantics.Move) (k : ℤ) (m : ℕ)
    (hits : (groupRun pre originalStart).2 = second k) :
    groupRun (pre ++ viaY k m (groupRun pre originalStart).1 (flipSign k (groupRun pre originalStart).1))
      originalStart = initial m := by
  have ht := project_after_hit pre k hits
  rw [groupRun_append]
  generalize ha : groupRun pre originalStart = s at *
  rcases s with ⟨a,b⟩
  change b = second k at hits
  subst b
  exact viaY_works k m a _ ht

theorem fixed_R_projects (k : ℤ) : project k originalR = Y := by
  rw [project_as_power]
  have hx : exponent 0 originalR = 0 := by decide +kernel
  have hy : exponent 1 originalR = -1 := by decide +kernel
  simp [hx,hy,Y]

/-- The entire legacy fixed-R family (all integer k) has a concrete route to D3. -/
theorem fixed_R_to_D3 (k : ℤ) :
    groupRun (viaY k 3 originalR false) (originalR,second k) = D3 := by
  exact viaY_works k 3 originalR false (fixed_R_projects k)

theorem fixed_R_to_family (n : ℕ) :
    groupRun (connector n originalR (uFamily n)) (originalR,vFamily n) = initial n := by
  simpa only [second_nat,initial] using connector_works n originalR (uFamily n)
    ((fixed_R_projects n).trans (project_initial_first n).symm)

end Verify.OneRelatorEntry
