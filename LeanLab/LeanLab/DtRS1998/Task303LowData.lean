/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Certificate294
import LeanLab.DtRS1998.Pock

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Offsets of certified candidates for the first reported block, page 210. -/
def offsets : List ℕ := [23, 39, 47, 53, 71, 77, 89, 149, 221, 243, 299, 339, 383, 389, 399, 411, 509, 519, 521, 537, 551, 581, 591, 593, 611, 687, 729, 761, 767, 779, 831, 891, 899, 917, 927, 933, 959, 977, 989, 1001, 1013, 1067, 1073, 1131, 1163, 1181, 1187, 1209, 1361, 1373, 1383, 1421, 1431, 1439, 1577, 1601, 1617, 1631, 1647, 1653, 1659, 1673, 1691, 1731, 1773, 1787, 1809, 1829, 1869, 1871, 1907, 1941, 1961, 1989, 2007, 2021, 2037, 2063, 2079, 2151, 2157, 2201, 2247, 2249, 2271, 2301, 2303, 2333, 2367, 2373, 2397, 2417, 2423, 2433, 2481, 2553, 2601, 2619, 2627, 2643, 2661, 2679, 2703, 2721, 2741, 2747, 2751, 2753, 2777, 2819, 2859, 2891, 2901, 2903, 2907, 2913, 2931, 3017, 3029, 3047, 3081, 3099, 3119, 3161, 3173, 3243, 3251, 3299, 3321, 3363, 3413, 3441, 3491, 3573, 3623, 3627, 3713, 3719, 3731, 3741, 3743, 3777, 3809, 3819, 3839, 3843, 3867, 3897, 3909, 3921, 3963, 3977, 3999, 4043, 4071, 4107, 4133, 4139, 4161, 4167, 4169, 4173, 4233, 4239, 4247, 4287, 4289, 4301, 4307, 4419, 4431, 4439, 4487, 4529, 4607, 5157, 5271, 5427]

/-- Large prime candidates for the first block, pages 209 and 210. -/
def qs : List ℕ := offsets.map (fun d => 400000000000 - d)

/-- Every shift is below the base, page 210. -/
theorem offset_bounds : ∀ d ∈ offsets, d ≤ 400000000000 := by decide +kernel

#print axioms offset_bounds

end LeanLab.DtRS1998.Task303.Low
