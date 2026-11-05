/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Certificate294
import LeanLab.DtRS1998.Pock

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Offsets of certified candidates for the first reported block, page 210. -/
def offsets : List ℕ := [1, 89, 131, 133, 163, 283, 289, 293, 331, 407, 409, 413, 427, 433, 479, 497, 509, 601, 607, 623, 647, 679, 691, 733, 751, 761, 779, 821, 901, 913, 923, 1003, 1007, 1037, 1109, 1163, 1219, 1279, 1283, 1357, 1417, 1441, 1463, 1469, 1483, 1517, 1547, 1603, 1627, 1639, 1679, 1709, 1741, 1771, 1837, 1877, 1913, 1961, 2011, 2017, 2033, 2047, 2053, 2059, 2071, 2081, 2213, 2221, 2267, 2311, 2333, 2347, 2369, 2371, 2393, 2407, 2471, 2479, 2483, 2561, 2609, 2659, 2663, 2683, 2693, 2707, 2749, 2759, 2831, 2891, 2893, 2899, 2971, 3013, 3017, 3043, 3067, 3071, 3121, 3179, 3181, 3223, 3233, 3257, 3269, 3277, 3299, 3341, 3461, 3521, 3527, 3599, 3611, 3617, 3641, 3667, 3671, 3677, 3727, 3733, 3829, 3881, 3937, 3953, 3967, 4037, 4091, 4121, 4123, 4139, 4159, 4189, 4213, 4217, 4279, 4331, 4357, 4369, 4381, 4387, 4433, 4459, 4499, 4501, 4523, 4541, 4553, 4577, 4607, 4627, 4633, 4681, 4747, 4769, 4781, 4789, 4793, 4817, 4931, 4937, 4963, 4991, 5017, 5033, 5059, 5167, 5287, 5881, 5929, 5983]

/-- Large prime candidates for the first block, pages 209 and 210. -/
def qs : List ℕ := offsets.map (fun d => 60000000000000 - d)

/-- Every shift is below the base, page 210. -/
theorem offset_bounds : ∀ d ∈ offsets, d ≤ 60000000000000 := by decide +kernel

#print axioms offset_bounds

end LeanLab.DtRS1998.Task303.Middle2
