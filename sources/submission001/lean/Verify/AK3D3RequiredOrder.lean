import Verify.AK3SixPointObstruction

/-! Every successful original-F S-to-D3 list has a y/Y conjugation of either
component strictly before a later second-component mixing move (ID4 or5).
The two moves need not be adjacent. No length or count bound is assumed. -/
namespace Verify.AK3D3RequiredOrder
open Verify.AtomicSemantics
open Verify.AK3Mod5FixedPointAdapter
open Verify.AK3SecondComponentTrace
open Verify.AK3D3HRowConnection
open Verify.AK3SixPointObstruction

def YConjugation (m : Move) : Prop :=
  m = .m8 ∨ m = .m9 ∨ m = .m12 ∨ m = .m13

def SecondMixPresent (ms : List Move) : Prop := .m4 ∈ ms ∨ .m5 ∈ ms

def YBeforeSecondMix : List Move → Prop
  | [] => False
  | m::ms => (YConjugation m ∧ SecondMixPresent ms) ∨ YBeforeSecondMix ms

theorem noMix_of_no_present (ms : List Move) (h : ¬ SecondMixPresent ms) : NoSecondMix ms := by
  intro m hm
  constructor
  · intro he
    apply h
    left
    simpa only [he] using hm
  · intro he
    apply h
    right
    simpa only [he] using hm

theorem y_conjugation_not_mix (m : Move) (hy : YConjugation m) : m ≠ .m4 ∧ m ≠ .m5 := by
  rcases hy with rfl | rfl | rfl | rfl <;> constructor <;> decide

theorem x_conjugation_of_not_y (m : Move)
    (hc : isConjugation m = true) (hy : ¬ YConjugation m) : XConjugation m := by
  cases m <;> simp_all [isConjugation,YConjugation,XConjugation]

theorem xOnly_cons_of_not_y (m : Move) (ms : List Move)
    (hy : ¬ YConjugation m) (hx : XOnlyTrace ms) : XOnlyTrace (m::ms) := by
  intro a ha
  have hh := List.mem_filter.mp ha
  rcases List.mem_cons.mp hh.1 with rfl | hm
  · exact x_conjugation_of_not_y _ hh.2 hy
  · exact hx a (List.mem_filter.mpr ⟨hm,hh.2⟩)

theorem split_of_no_order (ms : List Move) : ¬ YBeforeSecondMix ms →
    ∃ pre post : List Move, ms = pre ++ post ∧ XOnlyTrace pre ∧ NoSecondMix post := by
  induction ms with
  | nil =>
      intro _
      refine ⟨[],[],rfl,?_,?_⟩
      · simp [XOnlyTrace,conjugationTrace]
      · intro m hm
        cases hm
  | cons m ms ih =>
      intro h
      have ht : ¬ YBeforeSecondMix ms := fun hh => h (Or.inr hh)
      by_cases hy : YConjugation m
      · have hn : NoSecondMix ms :=
          noMix_of_no_present ms (fun hm => h (Or.inl ⟨hy,hm⟩))
        refine ⟨[],m::ms,rfl,?_,?_⟩
        · simp [XOnlyTrace,conjugationTrace]
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact y_conjugation_not_mix _ hy
          · exact hn a ha
      · rcases ih ht with ⟨pre,post,he,hx,hn⟩
        refine ⟨m::pre,post,?_,xOnly_cons_of_not_y m pre hy hx,hn⟩
        simpa only [List.cons_append] using congrArg (List.cons m) he

theorem success_requires_y_before_second_mix (ms : List Move)
    (h : groupRun ms originalStart = D3) : YBeforeSecondMix ms := by
  by_contra hn
  rcases split_of_no_order ms hn with ⟨pre,post,he,hx,hm⟩
  rw [he] at h
  exact no_split_D3 pre post hx hm h

theorem present_has_split (ms : List Move) (h : SecondMixPresent ms) :
    ∃ mid : List Move, ∃ b : Move, ∃ post : List Move,
      ms = mid ++ b::post ∧ (b = .m4 ∨ b = .m5) := by
  rcases h with h | h
  · rcases List.append_of_mem h with ⟨mid,post,he⟩
    exact ⟨mid,.m4,post,he,Or.inl rfl⟩
  · rcases List.append_of_mem h with ⟨mid,post,he⟩
    exact ⟨mid,.m5,post,he,Or.inr rfl⟩

theorem order_has_witness (ms : List Move) : YBeforeSecondMix ms →
    ∃ pre : List Move, ∃ a : Move, ∃ mid : List Move, ∃ b : Move, ∃ post : List Move,
      ms = pre ++ a::(mid ++ b::post) ∧ YConjugation a ∧ (b = .m4 ∨ b = .m5) := by
  induction ms with
  | nil => intro h; cases h
  | cons m ms ih =>
      intro h
      rcases h with ⟨hy,hm⟩ | ht
      · rcases present_has_split ms hm with ⟨mid,b,post,he,hb⟩
        exact ⟨[],m,mid,b,post,by simpa only [List.nil_append] using congrArg (List.cons m) he,hy,hb⟩
      · rcases ih ht with ⟨pre,a,mid,b,post,he,hy,hb⟩
        refine ⟨m::pre,a,mid,b,post,?_,hy,hb⟩
        simpa only [List.cons_append] using congrArg (List.cons m) he

theorem success_has_ordered_moves (ms : List Move)
    (h : groupRun ms originalStart = D3) :
    ∃ pre : List Move, ∃ a : Move, ∃ mid : List Move, ∃ b : Move, ∃ post : List Move,
      ms = pre ++ a::(mid ++ b::post) ∧
      (a = .m8 ∨ a = .m9 ∨ a = .m12 ∨ a = .m13) ∧ (b = .m4 ∨ b = .m5) := by
  exact order_has_witness ms (success_requires_y_before_second_mix ms h)

end Verify.AK3D3RequiredOrder
