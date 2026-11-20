import FixedSWitness

namespace Candidate.AK3Peak.FixedS.ExitTransfer
open Verify.AtomicSemantics

def censusStart : WordState := (w! "YXYxyx", w! "YYYYxxx")
def standard : WordState := (w! "x", w! "y")
def E3 : WordState := (w! "XyyyxYYYY", w! "xxYYYYXyyyy")

def rotation : List Move := [.m6,.m8,.m6,.m10,.m10,.m10]
def exitMoves : List Move :=
  [.m6,.m9,.m9,.m9,.m9,.m5,.m13,.m13,.m13,.m13,.m2,
   .m12,.m12,.m12,.m12,.m3,.m4,.m2,.m5,.m2,.m8]

theorem rotation_ok : Witness 13 censusStart ak3 rotation ∧
    rotation.length = 6 ∧ peak rotation censusStart = 13 := by
  unfold Witness
  decide +kernel

theorem exit_ok : Witness 22 E3 standard exitMoves ∧ exitMoves.length = 21 ∧
    peak exitMoves E3 = 22 := by
  unfold Witness
  decide +kernel

def Reaches (h : Nat) (s t : WordState) : Prop := ∃ ms, Witness h s t ms

private theorem liftCap {a h : Nat} {s t : WordState} {ms : List Move}
    (ah : a ≤ h) (w : Witness a s t ms) : Witness h s t ms := ⟨w.1, w.2.trans ah⟩

private theorem chain {h : Nat} {s t u : WordState} (a : Reaches h s t)
    (b : Reaches h t u) : Reaches h s u := by
  obtain ⟨xs,hx⟩ := a
  obtain ⟨ys,hy⟩ := b
  exact ⟨xs ++ ys, witness_append hx hy⟩

/-- Equivalence at each cap separately. No computation of a capped component is assumed. -/
theorem exit_iff (h : Nat) (hh : 22 ≤ h) :
    Reaches h source E3 ↔ Reaches h ak3 standard := by
  have hr : ReducedState E3 := by
    constructor <;> apply FreeGroup.IsReduced.of_reduce_eq <;> decide +kernel
  constructor
  · intro w
    exact chain (chain ⟨_, liftCap hh Bridge42.forward_ok⟩ w) ⟨_, liftCap hh exit_ok.1⟩
  · intro w
    exact chain (chain ⟨_, liftCap hh Bridge42.backward_ok⟩ w)
      ⟨_, liftCap hh (witness_reverse hr exit_ok.1)⟩

theorem census_iff (h : Nat) (hh : 13 ≤ h) : Reaches h censusStart standard ↔ Reaches h ak3 standard := by
  have hr : ReducedState censusStart := by
    constructor <;> apply FreeGroup.IsReduced.of_reduce_eq <;> decide +kernel
  constructor
  · exact chain ⟨_, liftCap hh (witness_reverse hr rotation_ok.1)⟩
  · exact chain ⟨_, liftCap hh rotation_ok.1⟩

/-- A route to S transfers to a route to A at the same cap, and conversely. -/
theorem target_iff (h : Nat) (hh : 22 ≤ h) (p : WordState) :
    Reaches h p source ↔ Reaches h p ak3 := by
  constructor
  · intro w
    exact chain w ⟨_, liftCap hh Bridge42.backward_ok⟩
  · intro w
    exact chain w ⟨_, liftCap hh Bridge42.forward_ok⟩

/-- The premise states the external cap-28 claim on literal ordered pairs. -/
theorem excluded_at_28_of_ak3 (ha : ¬ Reaches 28 ak3 standard) : ¬ Reaches 28 source E3 :=
  fun h => ha ((exit_iff 28 (by decide)).mp h)

#print axioms exit_ok
#print axioms rotation_ok
#print axioms exit_iff
#print axioms target_iff
#print axioms census_iff
#print axioms excluded_at_28_of_ak3

end Candidate.AK3Peak.FixedS.ExitTransfer
