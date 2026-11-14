import Verify.AK3D3HRowConnection

/-! Connect an actual chronological forward list and suffix with the reverse
boundary. This is a conditional original-F branch exclusion, not unrestricted
S-to-D3 nonreachability or a derivation of the effective-H condition.
-/
namespace Verify.AK3D3BranchConnection
open Verify.AtomicSemantics
open Verify.AK3Mod5FixedPointAdapter
open Verify.AK3SecondComponentTrace
open Verify.AK3D3HRowClassifier
open Verify.AK3D3HRowConnection

def inverseMove : Move → Move
  | .m0 => .m0 | .m1 => .m1
  | .m2 => .m3 | .m3 => .m2 | .m4 => .m5 | .m5 => .m4
  | .m6 => .m7 | .m7 => .m6 | .m8 => .m9 | .m9 => .m8
  | .m10 => .m11 | .m11 => .m10 | .m12 => .m13 | .m13 => .m12

def inverseMoves (ms : List Move) : List Move := ms.reverse.map inverseMove

theorem groupStep_inverse (m : Move) (s : GroupState) :
    groupStep (inverseMove m) (groupStep m s) = s := by
  rcases s with ⟨u,v⟩
  cases m <;> simp [inverseMove, groupStep, Verify.X, Verify.Y, mul_assoc]

theorem inverseMoves_cons (m : Move) (ms : List Move) :
    inverseMoves (m::ms) = inverseMoves ms ++ [inverseMove m] := by
  simp [inverseMoves]

theorem groupRun_append (pre post : List Move) (s : GroupState) :
    groupRun (pre ++ post) s = groupRun post (groupRun pre s) := by
  induction pre generalizing s with
  | nil => rfl
  | cons m ms ih => simpa only [List.cons_append, groupRun] using ih (groupStep m s)

theorem groupRun_inverse (ms : List Move) (s : GroupState) :
    groupRun (inverseMoves ms) (groupRun ms s) = s := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
      rw [groupRun, inverseMoves_cons, groupRun_append, ih]
      simpa only [groupRun] using groupStep_inverse m s

theorem no_complete_path_of_reverse_tail_constraints (pre post : List Move) (a b : Move)
    (hx : XOnlyTrace pre) (hn : NoSecondMix (inverseMoves post))
    (ht : conjugationTrace (inverseMoves post) = [a,b])
    (hH : AllowedD3H a b) : groupRun (pre ++ post) originalStart ≠ D3 := by
  intro h
  have heq := congrArg (groupRun (inverseMoves post)) h
  rw [groupRun_append, groupRun_inverse] at heq
  exact no_boundary_of_tail_constraints pre (inverseMoves post) a b hx hn ht hH heq

theorem no_complete_path_of_positive_reverse_trace (pre post : List Move) (i : Fin 8)
    (hx : XOnlyTrace pre) (hn : NoSecondMix (inverseMoves post))
    (ht : conjugationTrace (inverseMoves post) = positiveRowMoves i) :
    groupRun (pre ++ post) originalStart ≠ D3 := by
  intro h
  have heq := congrArg (groupRun (inverseMoves post)) h
  rw [groupRun_append, groupRun_inverse] at heq
  exact no_boundary_of_positive_trace pre (inverseMoves post) i hx hn ht heq

end Verify.AK3D3BranchConnection
