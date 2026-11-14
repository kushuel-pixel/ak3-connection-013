import Verify.AK3D3FixedPointTransport

/-! Exact free-group boundary conditions for the ten surviving total-conjugation
pairs. All ten already hit the complete mod5 target image with the bare pair;
the image cannot by itself remove any of them. No S-to-D3 route is asserted. -/
namespace Verify.AK3D3ResidualBoundary
open Verify.AtomicSemantics
open Verify.PermutationFixedPointNielsen
open Verify.AK3Mod5FixedPoint
open Verify.AK3Mod5FixedPointAdapter
open Verify.AK3SecondComponentTrace
open Verify.AK3D3HRowClassifier
open Verify.AK3D3HRowConnection
open Verify.AK3D3BranchConnection
open Verify.AK3D3FixedPointTransport

def residualConjugator (i : Fin 3) : Verify.F :=
  match i.val with
  | 0 => Verify.y | 1 => Verify.y*Verify.x | _ => Verify.y*Verify.X

def residualIndex (i j : Fin 8) : Fin 3 :=
  if i.val = 4 ∧ j.val = 6 then 1 else
    if i.val = 5 ∧ j.val = 6 then 2 else 0

def boundaryTarget (i : Fin 3) : Verify.F :=
  (residualConjugator i)⁻¹ * originalT false * residualConjugator i

def boundaryWord (i : Fin 3) (negative : Bool) : Verify.F := signed negative (boundaryTarget i)

def sixBoundaryWords : List Verify.F :=
  (List.finRange 3).flatMap (fun i => [boundaryWord i false,boundaryWord i true])

theorem signed_involutive (negative : Bool) (v : Verify.F) :
    signed negative (signed negative v) = v := by
  cases negative <;> simp [signed]

theorem success_boundary_second (pre post : List Move)
    (hn : NoSecondMix post)
    (h : groupRun (pre ++ post) originalStart = D3) :
    (groupRun pre originalStart).2 = signed (secondNegative post)
      ((secondConjugator post)⁻¹ * originalT false * secondConjugator post) := by
  have he := congrArg Prod.snd h
  rw [groupRun_append] at he
  have hs := groupRun_second_form post (groupRun pre originalStart) hn
  have hc : secondConjugator post *
      signed (secondNegative post) (groupRun pre originalStart).2 *
      (secondConjugator post)⁻¹ = originalT false := hs.symm.trans he
  have hv := congrArg (fun v : Verify.F => (secondConjugator post)⁻¹ * v * secondConjugator post) hc
  have hv' : signed (secondNegative post) (groupRun pre originalStart).2 =
      (secondConjugator post)⁻¹ * originalT false * secondConjugator post := by
    simpa [mul_assoc] using hv
  have hi := congrArg (signed (secondNegative post)) hv'
  simpa only [signed_involutive] using hi

theorem passing_pair_conjugator : ∀ i j : Fin 8, pairPasses i j = true →
    secondConjugator [conjugationMove i,conjugationMove j] =
      residualConjugator (residualIndex i j) := by decide

theorem success_residual_conjugator (pre post : List Move) (i j : Fin 8)
    (hx : XOnlyTrace pre) (hn : NoSecondMix post)
    (ht : conjugationTrace post = [conjugationMove i,conjugationMove j])
    (h : groupRun (pre ++ post) originalStart = D3) :
    secondConjugator post = residualConjugator (residualIndex i j) := by
  rw [secondConjugator_trace,ht]
  exact passing_pair_conjugator i j (two_conjugations_must_pass pre post i j hx hn ht h)

theorem success_requires_boundary_word (pre post : List Move) (i j : Fin 8)
    (hx : XOnlyTrace pre) (hn : NoSecondMix post)
    (ht : conjugationTrace post = [conjugationMove i,conjugationMove j])
    (h : groupRun (pre ++ post) originalStart = D3) :
    (groupRun pre originalStart).2 = boundaryWord (residualIndex i j) (secondNegative post) := by
  have hb := success_boundary_second pre post hn h
  rw [success_residual_conjugator pre post i j hx hn ht h] at hb
  exact hb

theorem boundaryTarget_explicit :
    boundaryTarget 0 = Verify.Y*Verify.x*Verify.Y^2 ∧
    boundaryTarget 1 = Verify.X*Verify.Y*Verify.x*Verify.Y^2*Verify.x ∧
    boundaryTarget 2 = Verify.x*Verify.Y*Verify.x*Verify.Y^2*Verify.X := by
  simp [boundaryTarget,residualConjugator,originalT,Verify.X,Verify.Y,pow_succ,mul_assoc]

theorem sixBoundaryWords_length : sixBoundaryWords.length = 6 := by decide

theorem sixBoundaryWords_nodup : sixBoundaryWords.Nodup := by decide

theorem six_boundary_codes :
    sixBoundaryWords.map (fun w => encodeWord (FreeGroup.toWord w)) =
      [[-2,1,-2,-2],[2,2,-1,2],
       [-1,-2,1,-2,-2,1],[-1,2,2,-1,2,1],
       [1,-2,1,-2,-2,-1],[1,2,2,-1,2,-1]] := by decide

theorem residual_group_count : ∀ i : Fin 3,
    allConjugationPairs.countP (fun ij => pairPasses ij.1 ij.2 &&
      decide (residualIndex ij.1 ij.2 = i)) = (if i.val = 0 then 8 else 1) := by decide

theorem boundaryWord_mem : ∀ (i : Fin 3) (negative : Bool),
    boundaryWord i negative ∈ sixBoundaryWords := by decide

theorem success_requires_six_boundary (pre post : List Move) (i j : Fin 8)
    (hx : XOnlyTrace pre) (hn : NoSecondMix post)
    (ht : conjugationTrace post = [conjugationMove i,conjugationMove j])
    (h : groupRun (pre ++ post) originalStart = D3) :
    (groupRun pre originalStart).2 ∈ sixBoundaryWords := by
  rw [success_requires_boundary_word pre post i j hx hn ht h]
  exact boundaryWord_mem _ _

theorem no_d3_of_boundary_not_six (pre post : List Move) (i j : Fin 8)
    (hx : XOnlyTrace pre) (hn : NoSecondMix post)
    (ht : conjugationTrace post = [conjugationMove i,conjugationMove j])
    (hb : (groupRun pre originalStart).2 ∉ sixBoundaryWords) :
    groupRun (pre ++ post) originalStart ≠ D3 := by
  intro h
  exact hb (success_requires_six_boundary pre post i j hx hn ht h)

theorem image_D3 : imagePair D3 = (r5,t5 false) := by
  apply Prod.ext
  · exact image_R
  · exact image_T false

theorem pair_image_pointwise : ∀ i j : Fin 8,
    ((∀ p : Point, (run14 ([conjugationMove i,conjugationMove j].map moveIndex) start).1 p = r5 p) ∧
     (∀ p : Point, (run14 ([conjugationMove i,conjugationMove j].map moveIndex) start).2 p = t5 false p)) ↔
      pairPasses i j = true := by decide

theorem pair_image_exact (i j : Fin 8) :
    run14 ([conjugationMove i,conjugationMove j].map moveIndex) start = (r5,t5 false) ↔
      pairPasses i j = true := by
  constructor
  · intro h
    apply (pair_image_pointwise i j).mp
    constructor <;> intro p
    · exact congrArg (fun s : Pair Point => s.1 p) h
    · exact congrArg (fun s : Pair Point => s.2 p) h
  · intro h
    rcases (pair_image_pointwise i j).mpr h with ⟨h1,h2⟩
    exact Prod.ext (Equiv.ext h1) (Equiv.ext h2)

theorem actual_pair_image_exact (i j : Fin 8) :
    imagePair (groupRun [conjugationMove i,conjugationMove j] originalStart) = imagePair D3 ↔
      pairPasses i j = true := by
  rw [image_run14,image_start,image_D3]
  exact pair_image_exact i j

theorem bare_pair_not_D3 : ∀ i j : Fin 8,
    groupRun [conjugationMove i,conjugationMove j] originalStart ≠ D3 := by decide

end Verify.AK3D3ResidualBoundary
