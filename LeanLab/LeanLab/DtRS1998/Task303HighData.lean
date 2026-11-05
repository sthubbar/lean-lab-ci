/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Certificate294
import LeanLab.DtRS1998.Pock

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Offsets of certified candidates for the first reported block, page 210. -/
def offsets : List ℕ := [7, 23, 59, 109, 113, 161, 187, 197, 217, 247, 323, 353, 361, 397, 403, 449, 451, 499, 569, 589, 637, 661, 667, 691, 703, 709, 721, 773, 781, 791, 803, 821, 829, 907, 931, 967, 1027, 1061, 1079, 1099, 1121, 1129, 1139, 1229, 1277, 1313, 1339, 1367, 1397, 1463, 1519, 1571, 1573, 1583, 1613, 1633, 1643, 1667, 1733, 1739, 1753, 1801, 1831, 1849, 1877, 1951, 1957, 1999, 2069, 2111, 2137, 2227, 2249, 2291, 2357, 2381, 2489, 2593, 2627, 2633, 2647, 2671, 2759, 2761, 2837, 2861, 2863, 2867, 2893, 2899, 2957, 2971, 3017, 3031, 3077, 3097, 3139, 3151, 3167, 3173, 3179, 3259, 3283, 3293, 3299, 3371, 3409, 3419, 3421, 3439, 3473, 3551, 3571, 3581, 3619, 3623, 3659, 3671, 3749, 3767, 3781, 3799, 3811, 3893, 3983, 4097, 4139, 4181, 4189, 4223, 4273, 4277, 4301, 4313, 4351, 4387, 4397, 4447, 4477, 4499, 4541, 4543, 4547, 4559, 4571, 4579, 4583, 4603, 4609, 4631, 4681, 4691, 4711, 4751, 4817, 4823, 4879, 4993, 4999, 5083, 5143, 5299, 5341, 5411, 5467, 5503, 5687, 5827, 5939, 5941, 6557]

/-- Large prime candidates for the first block, pages 209 and 210. -/
def qs : List ℕ := offsets.map (fun d => 90000000000000 - d)

/-- Every shift is below the base, page 210. -/
theorem offset_bounds : ∀ d ∈ offsets, d ≤ 90000000000000 := by decide +kernel

#print axioms offset_bounds

end LeanLab.DtRS1998.Task303.High
