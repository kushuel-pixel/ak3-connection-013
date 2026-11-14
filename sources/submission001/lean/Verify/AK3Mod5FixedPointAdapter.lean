import Verify.AtomicSemantics
import Verify.AK3Mod5FixedPoint

/-! Actual fixed14 groupRun adapter. The project AtomicSemantics is imported from
the pinned read-only cache; new proofs and objects stay in this isolated project.
The row-boundary theorem has an explicit image-classification premise.
-/
namespace Verify.AK3Mod5FixedPointAdapter
open Verify.AtomicSemantics
open Verify.PermutationFixedPointNielsen
open Verify.AK3Mod5FixedPoint

def image : Verify.F →* Equiv.Perm Point :=
  FreeGroup.lift (fun i : Fin 2 => if i = 0 then x5 else y5)

theorem image_x : image Verify.x = x5 := by
  change FreeGroup.lift (fun i : Fin 2 => if i = 0 then x5 else y5) (FreeGroup.of 0) = x5
  rw [FreeGroup.lift_apply_of]
  rfl

theorem image_y : image Verify.y = y5 := by
  change FreeGroup.lift (fun i : Fin 2 => if i = 0 then x5 else y5) (FreeGroup.of 1) = y5
  rw [FreeGroup.lift_apply_of]
  rfl

def imagePair (s : GroupState) : Pair Point := (image s.1,image s.2)

def moveIndex (m : Move) : Fin 14 :=
  ⟨moveId m, by cases m <;> decide⟩

theorem image_step (m : Move) (s : GroupState) :
    imagePair (groupStep m s) = act (step14 (moveIndex m)) (imagePair s) := by
  rcases s with ⟨u,v⟩
  cases m <;> apply Prod.ext <;>
    simp only [imagePair, groupStep, moveIndex, moveId, step14, act,
      Verify.X, Verify.Y, map_mul, map_inv, image_x, image_y, inv_inv]

theorem image_run (ms : List Move) (s : GroupState) :
    imagePair (groupRun ms s) =
      run (ms.map (fun m => step14 (moveIndex m))) (imagePair s) := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
      change imagePair (groupRun ms (groupStep m s)) =
        run (ms.map (fun m => step14 (moveIndex m)))
          (act (step14 (moveIndex m)) (imagePair s))
      rw [ih, image_step]

theorem image_run14 (ms : List Move) (s : GroupState) :
    imagePair (groupRun ms s) = run14 (ms.map moveIndex) (imagePair s) := by
  simpa only [run14, List.map_map, Function.comp_def] using image_run ms s

def originalR : Verify.F := Verify.X*Verify.y^3*Verify.x*Verify.Y^4
def originalB : Verify.F := Verify.x^2*Verify.Y^5*Verify.X*Verify.y^5
def originalT (negative : Bool) : Verify.F :=
  if negative then Verify.x*Verify.y^3 else Verify.x*Verify.Y^3
def originalStart : GroupState := (originalR,originalB)

theorem image_R : image originalR = r5 := by
  simp only [originalR, r5, Verify.X, Verify.Y, map_mul, map_pow, map_inv, image_x, image_y]

theorem image_B : image originalB = b5 := by
  simp only [originalB, b5, Verify.X, Verify.Y, map_mul, map_pow, map_inv, image_x, image_y]

theorem image_T (negative : Bool) : image (originalT negative) = t5 negative := by
  cases negative <;>
    simp only [originalT, t5, Bool.false_eq_true, ite_false, ite_true,
      Verify.Y, map_mul, map_pow, map_inv, image_x, image_y]

theorem image_start : imagePair originalStart = start := by
  apply Prod.ext
  · exact image_R
  · exact image_B

def SafeMoves (ms : List Move) : Prop := ∀ m ∈ ms, SafeId (moveIndex m)

theorem original_run_fixes (ms : List Move) (hm : SafeMoves ms) :
    BothFix (0 : Point) (imagePair (groupRun ms originalStart)) := by
  rw [image_run14, image_start]
  apply run14_fixes
  · intro i hi
    rcases List.mem_map.mp hi with ⟨m,hm',hEq⟩
    rw [← hEq]
    exact hm m hm'
  · exact start_fixes

theorem no_original_safe_target (ms : List Move) (hm : SafeMoves ms) (negative : Bool) :
    groupRun ms originalStart ≠ (originalR,originalT negative) := by
  intro h
  have hf := original_run_fixes ms hm
  rw [h] at hf
  have hpoint : image (originalT negative) (0 : Point) = 0 := hf.2
  rw [image_T] at hpoint
  have hnon : ∀ b : Bool, t5 b (0 : Point) ≠ 0 := by decide
  exact hnon negative hpoint

theorem no_original_row_boundary (ms qs : List Move) (hm : SafeMoves ms)
    (i : Fin 16) (inverse : Bool)
    (hrow : image ((groupRun qs (originalR,originalT (row i).negative)).2) =
      signedRowSecond i inverse) :
    groupRun ms originalStart ≠ groupRun qs (originalR,originalT (row i).negative) := by
  intro h
  have hf := original_run_fixes ms hm
  rw [h] at hf
  have hpoint : image ((groupRun qs (originalR,originalT (row i).negative)).2)
      (0 : Point) = 0 := hf.2
  rw [hrow] at hpoint
  exact all_rows_nonfix i inverse hpoint

end Verify.AK3Mod5FixedPointAdapter
