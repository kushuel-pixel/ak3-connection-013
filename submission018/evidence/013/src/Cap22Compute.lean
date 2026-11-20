import CompactEngine
import FixedSWitness
namespace Candidate.AK3Peak.FixedS
def deleted : AK3Compact.Ban := some (AK3Compact.encode U, AK3Compact.encode V)
theorem cap22_r17_r26 : AK3Compact.separate deleted 22 17 26 ak3 source = true := by decide +native
end Candidate.AK3Peak.FixedS
