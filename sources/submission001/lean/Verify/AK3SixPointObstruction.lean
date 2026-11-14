import Verify.AK3D3ResidualBoundary

/-! A six-point model excludes every x/X-only prefix followed by a suffix
without second-component mixing. No length or conjugation-count bound and no
effective-H or two-conjugation premise is used. The target second image is
a derangement, whereas the prefix second image has a fixed point. -/
namespace Verify.AK3SixPointObstruction
open Verify.AtomicSemantics
open Verify.PermutationFixedPointNielsen
open Verify.AK3Mod5FixedPointAdapter
open Verify.AK3SecondComponentTrace
open Verify.AK3D3HRowConnection
open Verify.AK3D3BranchConnection
open Verify.AK3D3ResidualBoundary

abbrev Point6 := Fin 6

def x6 : Equiv.Perm Point6 := Equiv.swap 2 3

def y6 : Equiv.Perm Point6 where
  toFun p := ⟨(p.val+1)%6, Nat.mod_lt _ (by decide)⟩
  invFun p := ⟨(p.val+5)%6, Nat.mod_lt _ (by decide)⟩
  left_inv := by
    intro p; apply Fin.ext
    exact (by decide : ∀ p : Point6, (((p.val+1)%6)+5)%6 = p.val) p
  right_inv := by
    intro p; apply Fin.ext
    exact (by decide : ∀ p : Point6, (((p.val+5)%6)+1)%6 = p.val) p

def r6 : Equiv.Perm Point6 := x6⁻¹*y6^3*x6*(y6⁻¹)^4
def b6 : Equiv.Perm Point6 := x6^2*(y6⁻¹)^5*x6⁻¹*y6^5
def t6 (negative : Bool) : Equiv.Perm Point6 :=
  if negative then x6*y6^3 else x6*(y6⁻¹)^3
def start6 : Pair Point6 := (r6,b6)

theorem x6_fixes_zero : x6 0 = 0 := by decide

theorem start6_fixes : BothFix (0 : Point6) start6 := by
  constructor <;> decide

theorem target6_no_fixed : ∀ (negative : Bool) (p : Point6), t6 negative p ≠ p := by decide

def image6 : Verify.F →* Equiv.Perm Point6 :=
  FreeGroup.lift (fun i : Fin 2 => if i = 0 then x6 else y6)

theorem image6_x : image6 Verify.x = x6 := by
  change FreeGroup.lift (fun i : Fin 2 => if i = 0 then x6 else y6) (FreeGroup.of 0) = x6
  rw [FreeGroup.lift_apply_of]
  rfl

theorem image6_y : image6 Verify.y = y6 := by
  change FreeGroup.lift (fun i : Fin 2 => if i = 0 then x6 else y6) (FreeGroup.of 1) = y6
  rw [FreeGroup.lift_apply_of]
  rfl

def imagePair6 (s : GroupState) : Pair Point6 := (image6 s.1,image6 s.2)

def step6 : Move → Step Point6
  | .m0 => .invU | .m1 => .invV | .m2 => .mulU | .m3 => .mulUInv
  | .m4 => .mulV | .m5 => .mulVInv
  | .m6 => .conjU x6 | .m7 => .conjU x6⁻¹
  | .m8 => .conjU y6 | .m9 => .conjU y6⁻¹
  | .m10 => .conjV x6 | .m11 => .conjV x6⁻¹
  | .m12 => .conjV y6 | .m13 => .conjV y6⁻¹

theorem image6_step (m : Move) (s : GroupState) :
    imagePair6 (groupStep m s) = act (step6 m) (imagePair6 s) := by
  rcases s with ⟨u,v⟩
  cases m <;> apply Prod.ext <;>
    simp only [imagePair6,groupStep,step6,act,Verify.X,Verify.Y,
      map_mul,map_inv,image6_x,image6_y,inv_inv]

theorem image6_run (ms : List Move) (s : GroupState) :
    imagePair6 (groupRun ms s) = run (ms.map step6) (imagePair6 s) := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
      change imagePair6 (groupRun ms (groupStep m s)) =
        run (ms.map step6) (act (step6 m) (imagePair6 s))
      rw [ih,image6_step]

theorem image6_R : image6 originalR = r6 := by
  simp only [originalR,r6,Verify.X,Verify.Y,map_mul,map_pow,map_inv,image6_x,image6_y]

theorem image6_B : image6 originalB = b6 := by
  simp only [originalB,b6,Verify.X,Verify.Y,map_mul,map_pow,map_inv,image6_x,image6_y]

theorem image6_T (negative : Bool) : image6 (originalT negative) = t6 negative := by
  cases negative <;>
    simp only [originalT,t6,Bool.false_eq_true,ite_false,ite_true,
      Verify.Y,map_mul,map_pow,map_inv,image6_x,image6_y]

theorem image6_start : imagePair6 originalStart = start6 := by
  exact Prod.ext image6_R image6_B

theorem step6_allowed (m : Move)
    (hm : isConjugation m = true → XConjugation m) : allowedAt (0 : Point6) (step6 m) := by
  cases m <;> simp_all [isConjugation,XConjugation,step6,allowedAt]
  all_goals decide

theorem prefix6_both_fix (pre : List Move) (hx : XOnlyTrace pre) :
    BothFix (0 : Point6) (imagePair6 (groupRun pre originalStart)) := by
  rw [image6_run,image6_start]
  apply run_fixes
  · intro a ha
    rcases List.mem_map.mp ha with ⟨m,hm,heq⟩
    rw [← heq]
    apply step6_allowed
    intro hc
    exact hx m (List.mem_filter.mpr ⟨hm,hc⟩)
  · exact start6_fixes

theorem image6_signed_fixes (negative : Bool) (v : Verify.F) (p : Point6)
    (hv : image6 v p = p) : image6 (signed negative v) p = p := by
  cases negative
  · exact hv
  · change image6 (v⁻¹) p = p
    rw [map_inv]
    exact fixes_inv (image6 v) p hv

theorem suffix6_second_fixes (post : List Move) (s : GroupState)
    (hn : NoSecondMix post) (p : Point6) (hv : image6 s.2 p = p) :
    image6 ((groupRun post s).2) (image6 (secondConjugator post) p) =
      image6 (secondConjugator post) p := by
  rw [groupRun_second_form post s hn,map_mul,map_mul,map_inv]
  exact Verify.PermutationFixedPoint.conjugate_fixes_of_maps
    (image6 (secondConjugator post)) (image6 (signed (secondNegative post) s.2))
    p (image6 (secondConjugator post) p) (image6_signed_fixes _ _ _ hv) rfl

theorem no_split_second_T (pre post : List Move) (negative : Bool)
    (hx : XOnlyTrace pre) (hn : NoSecondMix post) :
    (groupRun (pre ++ post) originalStart).2 ≠ originalT negative := by
  intro h
  have hp := (prefix6_both_fix pre hx).2
  have hf := suffix6_second_fixes post (groupRun pre originalStart) hn 0 hp
  rw [← groupRun_append,h,image6_T] at hf
  exact target6_no_fixed negative _ hf

theorem no_split_D3 (pre post : List Move)
    (hx : XOnlyTrace pre) (hn : NoSecondMix post) :
    groupRun (pre ++ post) originalStart ≠ D3 := by
  intro h
  exact no_split_second_T pre post false hx hn (congrArg Prod.snd h)

def boundaryImage6 (i : Fin 3) (negative : Bool) : Equiv.Perm Point6 :=
  let c := match i.val with
    | 0 => y6 | 1 => y6*x6 | _ => y6*x6⁻¹
  let v := c⁻¹*t6 false*c
  if negative then v⁻¹ else v

theorem image6_boundary (i : Fin 3) (negative : Bool) :
    image6 (boundaryWord i negative) = boundaryImage6 i negative := by
  rcases i with ⟨i,hi⟩
  interval_cases i <;> cases negative <;>
    simp [boundaryWord,boundaryTarget,residualConjugator,boundaryImage6,
      signed,Verify.X,map_mul,map_inv,image6_T,image6_x,image6_y]

theorem boundaryImage6_no_fixed : ∀ (i : Fin 3) (negative : Bool) (p : Point6),
    boundaryImage6 i negative p ≠ p := by decide

theorem no_prefix_boundaryWord (pre : List Move) (hx : XOnlyTrace pre)
    (i : Fin 3) (negative : Bool) :
    (groupRun pre originalStart).2 ≠ boundaryWord i negative := by
  intro h
  have hp := (prefix6_both_fix pre hx).2
  change image6 ((groupRun pre originalStart).2) (0 : Point6) = 0 at hp
  rw [h,image6_boundary] at hp
  exact boundaryImage6_no_fixed i negative 0 hp

theorem no_prefix_six_boundary (pre : List Move) (hx : XOnlyTrace pre) :
    (groupRun pre originalStart).2 ∉ sixBoundaryWords := by
  intro hm
  rcases List.mem_flatMap.mp hm with ⟨i,_,hi⟩
  simp only [List.mem_cons] at hi
  rcases hi with h | h | h
  · exact no_prefix_boundaryWord pre hx i false h
  · exact no_prefix_boundaryWord pre hx i true h
  · cases h

end Verify.AK3SixPointObstruction
