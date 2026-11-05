/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Certificate294
import LeanLab.DtRS1998.Pock

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Offsets of certified candidates for the first reported block, page 210. -/
def offsets : List ℕ := [3, 21, 43, 51, 63, 67, 87, 93, 129, 169, 171, 177, 183, 213, 219, 249, 301, 327, 357, 369, 451, 453, 519, 529, 597, 633, 673, 693, 739, 747, 751, 859, 873, 879, 883, 921, 931, 967, 981, 1069, 1083, 1107, 1117, 1129, 1159, 1173, 1179, 1209, 1239, 1317, 1339, 1353, 1363, 1401, 1407, 1423, 1449, 1509, 1519, 1543, 1557, 1591, 1629, 1633, 1653, 1677, 1687, 1779, 1783, 1837, 1863, 1867, 1897, 1899, 1929, 1933, 1941, 2019, 2073, 2107, 2109, 2133, 2137, 2149, 2167, 2229, 2247, 2313, 2377, 2391, 2431, 2497, 2523, 2551, 2557, 2577, 2587, 2593, 2689, 2707, 2709, 2791, 2829, 2851, 2863, 2877, 2881, 2889, 2947, 2983, 3061, 3109, 3157, 3171, 3223, 3229, 3253, 3267, 3349, 3379, 3393, 3433, 3451, 3481, 3483, 3489, 3519, 3523, 3547, 3591, 3669, 3739, 3741, 3781, 3787, 3853, 3913, 3939, 3951, 3957, 3973, 3999, 4069, 4191, 4243, 4267, 4411, 4417, 4467, 4471, 4573, 4587, 4597, 4603, 4617, 4639, 4707, 4711, 4723, 4753, 4797, 4923, 4971, 5043, 5161, 5191, 5217, 5869, 5919, 7561]

/-- Large prime candidates for the first block, pages 209 and 210. -/
def qs : List ℕ := offsets.map (fun d => 20000000000000 - d)

/-- Every shift is below the base, page 210. -/
theorem offset_bounds : ∀ d ∈ offsets, d ≤ 20000000000000 := by decide +kernel

#print axioms offset_bounds

end LeanLab.DtRS1998.Task303.Middle1
