import CountedHit

/-! A reusable entry theorem for any unimodular ordered relator pair.
The hypotheses contain no reachability assumption from S. -/
namespace Verify.EntryExtension
open AtomicSemantics OneRelatorEntry ResearchWords
open ROperationConnection (initial)
open SevenPrefixUpperBound (groupRun_append)
open Independent.CountedHit (coreCount class_of_count)

def UnitDet (s : GroupState) : Prop := det s = 1 ∨ det s = -1

instance unitDetDecidable (s : GroupState) : Decidable (UnitDet s) := by
  unfold UnitDet
  infer_instance

@[simp] theorem exponent_mul (i : Fin 2) (a b : F) :
    exponent i (a*b) = exponent i a + exponent i b := by simp [exponent]
@[simp] theorem exponent_inv (i : Fin 2) (a : F) :
    exponent i a⁻¹ = -exponent i a := by simp [exponent]
@[simp] theorem exponent_one (i : Fin 2) : exponent i 1 = 0 := by simp [exponent]
@[simp] theorem exponent_x0 : exponent 0 x = 1 := by decide +kernel
@[simp] theorem exponent_x1 : exponent 1 x = 0 := by decide +kernel
@[simp] theorem exponent_y0 : exponent 0 y = 0 := by decide +kernel
@[simp] theorem exponent_y1 : exponent 1 y = 1 := by decide +kernel
@[simp] theorem exponent_zpow (i : Fin 2) (a : F) (k : ℤ) :
    exponent i (a^k) = k * exponent i a := by
  cases k with
  | ofNat d => simp [exponent]
  | negSucc d =>
    change exponent i (a ^ (Int.negSucc d)) = (-((d:ℤ)+1)) * exponent i a
    simp [exponent, zpow_negSucc]
    ring

theorem determinant_step (m : Move) (s : GroupState) :
    det (groupStep m s) = if m = .m0 ∨ m = .m1 then -det s else det s := by
  rcases s with ⟨a,b⟩
  cases m <;> simp [groupStep,det,X,Y] <;> ring

theorem unit_run (ms : List Move) (s : GroupState) (h : UnitDet s) :
    UnitDet (groupRun ms s) := by
  induction ms generalizing s with
  | nil => exact h
  | cons m ms ih =>
    apply ih
    unfold UnitDet at *
    rw [determinant_step]
    split <;> rcases h with h|h <;> simp [h]

theorem original_unit : UnitDet AK3Mod5FixedPointAdapter.originalStart := by
  exact Or.inl (by decide +kernel)

theorem project_of_unit (a : F) (k : ℤ) (h : UnitDet (a,second k)) :
    project k a = if flipSign k a then y else Y := by
  have d : det (a,second k) = -(k*exponent 0 a + exponent 1 a) := by
    simp [det,second]
    ring
  unfold UnitDet at h
  rw [d] at h
  rw [project_as_power]
  rcases h with h|h
  · have e : k*exponent 0 a + exponent 1 a = -1 := by omega
    simp [flipSign,e,Y]
  · have e : k*exponent 0 a + exponent 1 a = 1 := by omega
    simp [flipSign,e]

theorem class_to_member (s : GroupState) (h : UnitDet s)
    (k : ℤ) (c : F) (neg : Bool) (m : ℕ)
    (hit : s.2 = c*(if neg then (second k)⁻¹ else second k)*c⁻¹) :
    ∃ tail : List Move, groupRun tail s = initial m := by
  let norm := normalizeSecond c neg
  have normalized : groupRun norm s = (s.1,second k) := by
    have pair : s = (s.1,c*(if neg then (second k)⁻¹ else second k)*c⁻¹) :=
      Prod.ext rfl hit
    rw [pair]
    exact normalizeSecond_run _ _ _ _
  have hu : UnitDet (s.1,second k) := by
    rw [← normalized]
    exact unit_run norm s h
  refine ⟨norm ++ viaY k m s.1 (flipSign k s.1), ?_⟩
  rw [groupRun_append, normalized]
  exact viaY_works k m s.1 _ (project_of_unit s.1 k hu)

theorem count_to_member (s : GroupState) (h : UnitDet s) (m : ℕ)
    (hit : coreCount s.2 = 1) :
    ∃ tail : List Move, groupRun tail s = initial m := by
  obtain ⟨k,c,n,e⟩ := class_of_count s.2 hit
  exact class_to_member s h k c n m e

theorem count_to_standard (s : GroupState) (h : UnitDet s)
    (hit : coreCount s.2 = 1) :
    ∃ tail : List Move, groupRun tail s = (x,y) := by
  obtain ⟨tail,e⟩ := count_to_member s h 0 hit
  refine ⟨tail ++ SevenPrefixUpperBound.word 0, ?_⟩
  rw [groupRun_append,e,SevenPrefixUpperBound.reaches]

end Verify.EntryExtension
