import Verify.AK3D3BranchConnection

/-! An arbitrary-length, arbitrary-conjugation-count necessary condition.
For an x/X-only prefix and a suffix without IDs4/5, the fixed point0
must be transported to the unique D3 second-word fixed point1.
No effective-H condition or two-conjugation assumption is used.
-/
namespace Verify.AK3D3FixedPointTransport
open Verify.AtomicSemantics
open Verify.PermutationFixedPointNielsen
open Verify.AK3Mod5FixedPoint
open Verify.AK3Mod5FixedPointAdapter
open Verify.AK3SecondComponentTrace
open Verify.AK3D3HRowClassifier
open Verify.AK3D3HRowConnection
open Verify.AK3D3BranchConnection

theorem d3_second_fixed_iff : ∀ p : Point, t5 false p = p ↔ p = 1 := by decide

theorem image_signed_fixes (negative : Bool) (v : Verify.F) (p : Point)
    (hv : image v p = p) : image (signed negative v) p = p := by
  cases negative
  · exact hv
  · change (image (v⁻¹)) p = p
    rw [map_inv]
    exact fixes_inv (image v) p hv

theorem second_run_fixes_transported_point (post : List Move) (s : GroupState)
    (hn : NoSecondMix post) (p : Point) (hv : image s.2 p = p) :
    image ((groupRun post s).2) (image (secondConjugator post) p) =
      image (secondConjugator post) p := by
  rw [groupRun_second_form post s hn, map_mul, map_mul, map_inv]
  exact Verify.PermutationFixedPoint.conjugate_fixes_of_maps
    (image (secondConjugator post)) (image (signed (secondNegative post) s.2))
    p (image (secondConjugator post) p) (image_signed_fixes _ _ _ hv) rfl

theorem d3_success_requires_conjugator_point (pre post : List Move)
    (hx : XOnlyTrace pre) (hn : NoSecondMix post)
    (h : groupRun (pre ++ post) originalStart = D3) :
    image (secondConjugator post) (0 : Point) = 1 := by
  have hp := (original_run_fixes pre (safeMoves_of_x_only_trace pre hx)).2
  have ht := second_run_fixes_transported_point post (groupRun pre originalStart) hn 0 hp
  rw [groupRun_append] at h
  rw [h] at ht
  change image (originalT false) (image (secondConjugator post) 0) =
    image (secondConjugator post) 0 at ht
  rw [image_T] at ht
  exact (d3_second_fixed_iff _).mp ht

def advancePoint (m : Move) (p : Point) : Point :=
  match m with
  | .m10 => x5 p | .m11 => x5⁻¹ p
  | .m12 => y5 p | .m13 => y5⁻¹ p
  | _ => p

def transportPoint : List Move → Point → Point
  | [],p => p
  | m::ms,p => transportPoint ms (advancePoint m p)

theorem advancePoint_eq_image_secondLetter (m : Move) (p : Point) :
    advancePoint m p = image (secondLetter m) p := by
  cases m <;> simp [advancePoint, secondLetter, Verify.X, Verify.Y,
    image_x, image_y, map_inv]

theorem transportPoint_eq_conjugator_image (ms : List Move) (p : Point) :
    transportPoint ms p = image (secondConjugator ms) p := by
  induction ms generalizing p with
  | nil => simp [transportPoint, secondConjugator]
  | cons m ms ih =>
      simp [transportPoint, secondConjugator, ih, advancePoint_eq_image_secondLetter,
        map_mul, Equiv.Perm.mul_apply]

theorem transportPoint_append (pre post : List Move) (p : Point) :
    transportPoint (pre ++ post) p = transportPoint post (transportPoint pre p) := by
  induction pre generalizing p with
  | nil => rfl
  | cons m ms ih => simpa only [List.cons_append, transportPoint] using ih (advancePoint m p)

theorem transportPoint_trace (ms : List Move) (p : Point) :
    transportPoint (conjugationTrace ms) p = transportPoint ms p := by
  rw [transportPoint_eq_conjugator_image, ← secondConjugator_trace,
    transportPoint_eq_conjugator_image]

theorem d3_success_requires_transport (pre post : List Move)
    (hx : XOnlyTrace pre) (hn : NoSecondMix post)
    (h : groupRun (pre ++ post) originalStart = D3) : transportPoint post 0 = 1 := by
  rw [transportPoint_eq_conjugator_image]
  exact d3_success_requires_conjugator_point pre post hx hn h

theorem no_d3_of_transport_ne (pre post : List Move)
    (hx : XOnlyTrace pre) (hn : NoSecondMix post)
    (hp : transportPoint post 0 ≠ 1) : groupRun (pre ++ post) originalStart ≠ D3 := by
  intro h
  exact hp (d3_success_requires_transport pre post hx hn h)

theorem advancePoint_inverse (m : Move) (p : Point) :
    advancePoint (inverseMove m) (advancePoint m p) = p := by
  cases m <;> simp [advancePoint, inverseMove, Equiv.Perm.inv_def]

theorem transportPoint_inverseMoves (ms : List Move) (p : Point) :
    transportPoint (inverseMoves ms) (transportPoint ms p) = p := by
  induction ms generalizing p with
  | nil => rfl
  | cons m ms ih =>
      rw [transportPoint, inverseMoves_cons, transportPoint_append, ih]
      simpa only [transportPoint] using advancePoint_inverse m p

def pairPasses (i j : Fin 8) : Bool :=
  decide (transportPoint [conjugationMove i,conjugationMove j] 0 = 1)

theorem two_conjugations_must_pass (pre post : List Move) (i j : Fin 8)
    (hx : XOnlyTrace pre) (hn : NoSecondMix post)
    (ht : conjugationTrace post = [conjugationMove i,conjugationMove j])
    (h : groupRun (pre ++ post) originalStart = D3) : pairPasses i j = true := by
  have hp := d3_success_requires_transport pre post hx hn h
  have hpair : transportPoint [conjugationMove i,conjugationMove j] 0 = 1 := by
    rw [← ht, transportPoint_trace]
    exact hp
  simp [pairPasses, hpair]

theorem no_d3_of_blocked_conjugation_pair (pre post : List Move) (i j : Fin 8)
    (hx : XOnlyTrace pre) (hn : NoSecondMix post)
    (ht : conjugationTrace post = [conjugationMove i,conjugationMove j])
    (hb : pairPasses i j = false) : groupRun (pre ++ post) originalStart ≠ D3 := by
  intro h
  have hp := two_conjugations_must_pass pre post i j hx hn ht h
  rw [hb] at hp
  contradiction

theorem pairPasses_exact : ∀ i j : Fin 8, pairPasses i j = true ↔
    (i.val ≤ 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val ≤ 3) := by decide

def allConjugationPairs : List (Fin 8 × Fin 8) :=
  (List.finRange 8).flatMap (fun i => (List.finRange 8).map (fun j => (i,j)))

theorem passing_pair_count :
    (allConjugationPairs.countP (fun ij => pairPasses ij.1 ij.2)) = 10 := by decide

theorem blocked_pair_count :
    (allConjugationPairs.countP (fun ij => !(pairPasses ij.1 ij.2))) = 54 := by decide

theorem old_eight_forward_traces_blocked : ∀ i : Fin 8,
    transportPoint (inverseMoves (positiveRowMoves i)) 0 ≠ 1 := by decide

theorem old_eight_reverse_traces_blocked : ∀ i : Fin 8,
    transportPoint (positiveRowMoves i) 1 ≠ 0 := by decide

theorem old_reverse_trace_forces_transport_ne (post : List Move) (i : Fin 8)
    (ht : conjugationTrace (inverseMoves post) = positiveRowMoves i) :
    transportPoint post 0 ≠ 1 := by
  intro hp
  have hi := transportPoint_inverseMoves post 0
  rw [hp] at hi
  rw [← transportPoint_trace (inverseMoves post) 1, ht] at hi
  exact old_eight_reverse_traces_blocked i hi

end Verify.AK3D3FixedPointTransport
