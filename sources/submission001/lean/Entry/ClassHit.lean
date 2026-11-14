import Entry.FixedTargets

namespace Verify.OneRelatorEntry
open AtomicSemantics ResearchWords ROperationConnection
open AK3Mod5FixedPointAdapter (originalStart)
open AK3D3HRowConnection (D3)
open SevenPrefixUpperBound (groupRun_append)

private def stripLetter (l : Letter) : AtomicSemantics.Move :=
  if l.1 = 0 then (if l.2 then .m11 else .m10)
  else (if l.2 then .m13 else .m12)

private theorem strip_one (a b : F) (l : Letter) :
    groupStep (stripLetter l) (a,b) = (a,(FreeGroup.mk [l])⁻¹*b*FreeGroup.mk [l]) := by
  rcases l with ⟨i,s⟩
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> cases s
  · change (a,x*b*X) = (a,(x⁻¹)⁻¹*b*x⁻¹)
    simp [X]
  · rfl
  · change (a,y*b*Y) = (a,(y⁻¹)⁻¹*b*y⁻¹)
    simp [Y]
  · rfl

private theorem strip_word (q : Word) (a b : F) :
    groupRun (q.map stripLetter) (a,b) = (a,(FreeGroup.mk q)⁻¹*b*FreeGroup.mk q) := by
  induction q generalizing b with
  | nil => change (a,b) = (a,(1:F)⁻¹*b*1); simp
  | cons l q ih =>
    change groupRun _ (groupStep (stripLetter l) (a,b)) = _
    rw [strip_one,ih]
    change _ = (a,(FreeGroup.mk [l]*FreeGroup.mk q)⁻¹*b*(FreeGroup.mk [l]*FreeGroup.mk q))
    simp only [mul_inv_rev,mul_assoc]

def normalizeSecond (c : F) (neg : Bool) : List AtomicSemantics.Move :=
  c.toWord.map stripLetter ++ (if neg then [.m1] else [])

theorem normalizeSecond_run (a b c : F) (neg : Bool) :
    groupRun (normalizeSecond c neg) (a,c*(if neg then b⁻¹ else b)*c⁻¹) = (a,b) := by
  rw [normalizeSecond,groupRun_append,strip_word,FreeGroup.mk_toWord]
  cases neg <;> simp [groupRun,groupStep,mul_assoc]

theorem class_hit_to_member (pre : List AtomicSemantics.Move) (k : ℤ) (c : F) (neg : Bool) (m : ℕ)
    (hit : (groupRun pre originalStart).2 = c*(if neg then (second k)⁻¹ else second k)*c⁻¹) :
    ∃ tail : List AtomicSemantics.Move, groupRun (pre ++ tail) originalStart = initial m := by
  let norm := normalizeSecond c neg
  let p := pre ++ norm
  have normalized : groupRun p originalStart = ((groupRun pre originalStart).1,second k) := by
    have hp : groupRun pre originalStart =
        ((groupRun pre originalStart).1,c*(if neg then (second k)⁻¹ else second k)*c⁻¹) := Prod.ext rfl hit
    change groupRun (pre ++ norm) originalStart = _
    rw [groupRun_append]
    conv_lhs => rw [show groupRun pre originalStart =
      ((groupRun pre originalStart).1,c*(if neg then (second k)⁻¹ else second k)*c⁻¹) from hp]
    exact normalizeSecond_run _ _ _ _
  have second_ok := congrArg Prod.snd normalized
  have finish := signed_second_hit p k m second_ok
  refine ⟨norm ++ viaY k m (groupRun p originalStart).1 (flipSign k (groupRun p originalStart).1), ?_⟩
  simpa only [p,List.append_assoc] using finish

/-- This equivalence compares unbounded reachability, without a path-length or peak cap. -/
theorem d3_iff_second_class :
    (∃ ms : List AtomicSemantics.Move, groupRun ms originalStart = D3) ↔
      ∃ (pre : List AtomicSemantics.Move) (k : ℤ) (c : F) (neg : Bool),
        (groupRun pre originalStart).2 = c*(if neg then (second k)⁻¹ else second k)*c⁻¹ := by
  constructor
  · rintro ⟨ms,h⟩
    refine ⟨ms,3,1,false,?_⟩
    rw [h]
    have h3 : D3 = initial 3 := rfl
    rw [h3]
    change vFamily 3 = 1*(if false then _ else second (3:ℤ))*1⁻¹
    simpa using (second_nat 3).symm
  · rintro ⟨p,k,c,neg,h⟩
    obtain ⟨tail,ends⟩ := class_hit_to_member p k c neg 3 h
    exact ⟨p++tail,ends⟩

end Verify.OneRelatorEntry
