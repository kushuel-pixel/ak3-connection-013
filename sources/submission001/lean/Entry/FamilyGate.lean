import Entry.OneRelator

namespace Verify.OneRelatorEntry
open AtomicSemantics ResearchWords ROperationConnection
open SevenPrefixUpperBound (groupRun_append)

private theorem maps_agree {P Q : F →* F} (hx : P x = Q x) (hy : P y = Q y) : P = Q := by
  apply FreeGroup.lift.symm.injective
  funext i
  change P (FreeGroup.of i) = Q (FreeGroup.of i)
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · exact hx
  · exact hy

/-- A signed index for the primitive second word. -/
def second (k : ℤ) : F := x * (y^k)⁻¹

@[simp] theorem second_nat (n : ℕ) : second n = vFamily n := by
  simp [second,vFamily,Y]

/-- Coordinates for the basis (x Y^k, y). -/
def inBasis (n : ℤ) : F →* F := substitute (x * y^n) y

/-- The quotient obtained by setting x Y^n equal to one. -/
def project (n : ℤ) : F →* F := substitute (y^n) y

private theorem basis_back (n : ℤ) (a : F) : substitute (second n) y (inBasis n a) = a := by
  have h : (substitute (second n) y).comp (inBasis n) = MonoidHom.id F := by
    apply maps_agree
    · change substitute (second n) y (inBasis n x) = x
      simp [inBasis, second, mul_assoc]
    · change substitute (second n) y (inBasis n y) = y
      simp [inBasis]
  exact DFunLike.congr_fun h a

private theorem basis_project (n : ℤ) (a : F) : substitute 1 y (inBasis n a) = project n a := by
  have h : (substitute 1 y).comp (inBasis n) = project n := by
    apply maps_agree
    · change substitute 1 y (inBasis n x) = project n x
      simp [inBasis, project]
    · change substitute 1 y (inBasis n y) = project n y
      simp [inBasis, project]
  exact DFunLike.congr_fun h a

/-- The shortest reduced spelling of the correction in this basis is used.
No ac-r2-v1 distance or min-peak claim is made. -/
def correctionWord (n : ℤ) (a b : F) : Word := (inBasis n (a⁻¹*b)).toWord

def connector (n : ℤ) (a b : F) : List AtomicSemantics.Move := scan (correctionWord n a b)

theorem connector_length (n : ℤ) (a b : F) :
    (connector n a b).length = (correctionWord n a b).length := scan_length _

theorem connector_works (n : ℤ) (a b : F) (same : project n a = project n b) :
    groupRun (connector n a b) (a,second n) = (b,second n) := by
  have closed : substitute 1 y (FreeGroup.mk (correctionWord n a b)) = 1 := by
    rw [correctionWord, FreeGroup.mk_toWord, basis_project, map_mul, map_inv, same, inv_mul_cancel]
  rw [connector, scan_closed _ _ _ closed, correctionWord, FreeGroup.mk_toWord, basis_back]
  simp

theorem project_initial_first (n : ℕ) : project n (uFamily n) = Y := by
  simp [project,uFamily,X,Y,pow_succ,mul_assoc]

/-- An optional ID0 handles the other sign of the first relator. -/
def enter (n : ℕ) (a : F) (flip : Bool) : List AtomicSemantics.Move :=
  if flip then .m0 :: connector n a⁻¹ (uFamily n) else connector n a (uFamily n)

theorem enter_works (n : ℕ) (a : F) (flip : Bool)
    (test : project n a = if flip then y else Y) :
    groupRun (enter n a flip) (a,vFamily n) = initial n := by
  cases flip with
  | false => simpa [enter,initial,second_nat] using (connector_works n _ _ (test.trans (project_initial_first n).symm))
  | true =>
    change groupRun (connector n a⁻¹ (uFamily n)) (a⁻¹,vFamily n) = initial n
    rw [← second_nat]
    change groupRun (connector n a⁻¹ (uFamily n)) (a⁻¹,second n) = (uFamily n,vFamily n)
    rw [← second_nat]
    apply connector_works
    rw [map_inv, test, project_initial_first]
    rfl

theorem enter_then_family (n m : ℕ) (a : F) (flip : Bool)
    (test : project n a = if flip then y else Y) :
    groupRun (enter n a flip ++ AdjacentFamily.betweenMoves n m) (a,vFamily n) = initial m := by
  rw [groupRun_append, enter_works n a flip test, AdjacentFamily.between_run]

end Verify.OneRelatorEntry
