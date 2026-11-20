import FixedSWitness

namespace Candidate.AK3Peak.FixedS.ExitExample
open Verify.AtomicSemantics

def landing : WordState := (w! "yyyyxYXyxYYYxyyyy", w! "YYYYXXYYYYX")
def moves : List Move :=
  [.m1, .m12, .m12, .m12, .m11, .m4, .m13, .m11, .m4, .m9,
   .m4, .m3, .m6, .m8, .m8, .m8, .m8, .m3, .m0, .m6,
   .m8, .m13, .m13, .m13, .m4, .m9, .m12, .m12, .m12, .m10,
   .m0, .m7, .m2, .m11, .m13, .m13, .m13, .m13, .m3]

/-- Literal endpoint, exact peak and move count for the crossing from S to the landing. -/
theorem landing39_ok :
    Witness 29 source landing moves ∧ peak moves source = 29 ∧ moves.length = 39 ∧ total landing = 28 := by
  unfold Witness
  decide +kernel

#print axioms landing39_ok
end Candidate.AK3Peak.FixedS.ExitExample
