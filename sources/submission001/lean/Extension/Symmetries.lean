import Extension.UnitGate
import Verify.AK3D3BranchConnection

namespace Verify.EntryExtension
open AtomicSemantics OneRelatorEntry ResearchWords
open ROperationConnection (initial)
open SevenPrefixUpperBound (groupRun_append)

def Reach (s t : GroupState) : Prop := ∃ ms : List Move, groupRun ms s = t

theorem reach_trans {s t u : GroupState} (h : Reach s t) (k : Reach t u) : Reach s u := by
  obtain ⟨p,hp⟩ := h
  obtain ⟨q,hq⟩ := k
  exact ⟨p++q, by rw [groupRun_append,hp,hq]⟩

theorem reach_symm {s t : GroupState} (h : Reach s t) : Reach t s := by
  obtain ⟨p,hp⟩ := h
  refine ⟨AK3D3BranchConnection.inverseMoves p, ?_⟩
  rw [← hp]
  exact AK3D3BranchConnection.groupRun_inverse p s

def rows (s : GroupState) : GroupState := (s.2,s.1)
def rowMove : Move → Move
  | .m0 => .m1 | .m1 => .m0 | .m2 => .m4 | .m3 => .m5
  | .m4 => .m2 | .m5 => .m3 | .m6 => .m10 | .m7 => .m11
  | .m8 => .m12 | .m9 => .m13 | .m10 => .m6 | .m11 => .m7
  | .m12 => .m8 | .m13 => .m9

@[simp] theorem rows_twice (s : GroupState) : rows (rows s) = s := by
  cases s; rfl

theorem rows_step (m : Move) (s : GroupState) :
    groupStep (rowMove m) (rows s) = rows (groupStep m s) := by
  cases s
  cases m <;> rfl

theorem rows_run (ms : List Move) (s : GroupState) :
    groupRun (ms.map rowMove) (rows s) = rows (groupRun ms s) := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
    change groupRun (ms.map rowMove) (groupStep (rowMove m) (rows s)) = _
    rw [rows_step,ih]
    rfl

theorem determinant_rows (s : GroupState) : det (rows s) = -det s := by
  cases s
  simp [rows,det]
  ring

theorem unit_rows (s : GroupState) (h : UnitDet s) : UnitDet (rows s) := by
  unfold UnitDet at *
  rw [determinant_rows]
  rcases h with h|h <;> simp [h]

def rename : F →* F := substitute y x
@[simp] theorem rename_x : rename x = y := by simp [rename,substitute,x]
@[simp] theorem rename_y : rename y = x := by simp [rename,substitute,y]

@[simp] theorem rename_twice (g : F) : rename (rename g) = g := by
  induction g using FreeGroup.induction_on with
  | one => simp
  | of i =>
    rcases (show i = 0 ∨ i = 1 by omega) with rfl|rfl
    · change rename (rename x) = x
      simp
    · change rename (rename y) = y
      simp
  | inv_of i ih => simpa using congrArg Inv.inv ih
  | mul a b ha hb => simp [ha,hb]

def vars (s : GroupState) : GroupState := (rename s.1,rename s.2)
def varMove : Move → Move
  | .m6 => .m8 | .m7 => .m9 | .m8 => .m6 | .m9 => .m7
  | .m10 => .m12 | .m11 => .m13 | .m12 => .m10 | .m13 => .m11
  | m => m

@[simp] theorem vars_twice (s : GroupState) : vars (vars s) = s := by
  cases s
  simp [vars]

theorem vars_step (m : Move) (s : GroupState) :
    groupStep (varMove m) (vars s) = vars (groupStep m s) := by
  cases s
  cases m <;> simp [varMove,vars,groupStep,X,Y]

theorem vars_run (ms : List Move) (s : GroupState) :
    groupRun (ms.map varMove) (vars s) = vars (groupRun ms s) := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
    change groupRun (ms.map varMove) (groupStep (varMove m) (vars s)) = _
    rw [vars_step,ih]
    rfl

theorem exponent_rename (g : F) :
    exponent 0 (rename g) = exponent 1 g ∧ exponent 1 (rename g) = exponent 0 g := by
  induction g using FreeGroup.induction_on with
  | one => simp
  | of i =>
    rcases (show i = 0 ∨ i = 1 by omega) with rfl|rfl
    · change exponent 0 (rename x) = exponent 1 x ∧ exponent 1 (rename x) = exponent 0 x
      simp
    · change exponent 0 (rename y) = exponent 1 y ∧ exponent 1 (rename y) = exponent 0 y
      simp
  | inv_of i ih => simp_all
  | mul a b ha hb => simp_all

theorem determinant_vars (s : GroupState) : det (vars s) = -det s := by
  cases s with
  | mk a b =>
    simp only [vars,det]
    rw [(exponent_rename a).1,(exponent_rename a).2,
      (exponent_rename b).1,(exponent_rename b).2]
    ring

theorem unit_vars (s : GroupState) (h : UnitDet s) : UnitDet (vars s) := by
  unfold UnitDet at *
  rw [determinant_vars]
  rcases h with h|h <;> simp [h]

def swapStandard : List Move := .m0 :: SevenPrefixUpperBound.word 0

theorem swap_standard_run : groupRun swapStandard (y,x) = (x,y) := by
  change groupRun (SevenPrefixUpperBound.word 0) (Y,x) = (x,y)
  have h : (Y,x) = initial 0 := by simp [initial,uFamily,vFamily,X,Y]
  rw [h,SevenPrefixUpperBound.reaches]

theorem rows_to_standard (s : GroupState) (h : Reach (rows s) (x,y)) :
    Reach s (x,y) := by
  obtain ⟨ms,hm⟩ := h
  have e := rows_run ms (rows s)
  rw [rows_twice,hm] at e
  refine ⟨ms.map rowMove ++ swapStandard, ?_⟩
  rw [groupRun_append,e]
  exact swap_standard_run

theorem vars_to_standard (s : GroupState) (h : Reach (vars s) (x,y)) :
    Reach s (x,y) := by
  obtain ⟨ms,hm⟩ := h
  have e := vars_run ms (vars s)
  rw [vars_twice,hm] at e
  refine ⟨ms.map varMove ++ swapStandard, ?_⟩
  rw [groupRun_append,e]
  simpa [vars] using swap_standard_run

theorem standard_to_member (m : ℕ) : Reach (x,y) (initial m) := by
  apply reach_symm
  exact ⟨SevenPrefixUpperBound.word m,SevenPrefixUpperBound.reaches m⟩

end Verify.EntryExtension
