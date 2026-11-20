import BankEngine
import B5PeakCore
namespace Candidate.AK3Peak.FixedS
/-- Capacities affect only storage and run time. -/
def widths : List Nat := [134217728,33554432,8388608,2097152]
theorem cap26_r16_r24 : AK3Bank.separate widths none 26 16 24 ak3 source = true := by decide +native
end Candidate.AK3Peak.FixedS
