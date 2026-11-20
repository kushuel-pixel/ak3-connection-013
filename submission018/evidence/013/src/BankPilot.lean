import BankEngine
import B5PeakCore
namespace Candidate.AK3Peak.FixedS
-- Zero-width and deliberately undersized banks exercise fallback to the overflow table.
example : AK3Bank.separate [0,1,2] none 25 3 4 ak3 source = true := by decide +native
example : AK3Bank.separate [0,1,2] none 25 1 1 ak3 ak3 = false := by decide +native
example : (AK3Bank.ball [8192,2048] none 30 ak3 4).front.length = 9307 := by decide +native
end Candidate.AK3Peak.FixedS
