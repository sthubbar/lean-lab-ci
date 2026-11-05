/-
AI wrote this Lean code for CODEX task372.
P0037 pages 207, 211 and 213. Fixed row 100 small-complement checks.
This file asserts no primality of any large candidate.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.Decomp372c

set_option maxRecDepth 100000

/-- P0037 pages 211 and 213. Reconstructed offsets for the first 250
candidates in increasing candidate order from 10^100 - 68969.
This finite data definition asserts no primality or exact prime index. -/
def offsets : List ℕ := [68969, 68811, 68603, 68501, 68111, 67887, 67773, 67601, 67397, 66801, 66533, 66387, 66377, 66071, 65823, 65819, 65457, 65151, 65039, 65031, 64233, 63993, 63083, 62817, 62643, 62111, 62009, 61979, 61959, 61673, 61451, 61407, 61343, 61269, 60903, 60873, 60863, 60587, 60551, 60051, 59871, 59559, 59481, 59393, 59337, 58863, 58319, 57933, 57497, 56741, 56237, 56141, 55593, 55491, 55401, 55239, 54567, 54173, 54167, 53853, 53751, 53159, 53039, 52929, 52863, 52671, 52421, 52403, 52391, 52359, 52011, 51999, 51957, 51869, 51647, 51581, 51543, 51467, 51383, 51219, 50979, 50717, 49757, 49607, 49563, 49499, 49469, 49203, 49097, 49007, 48491, 48431, 48419, 48399, 48351, 48347, 48329, 48309, 47879, 47469, 47409, 46263, 46251, 45689, 45669, 45447, 45143, 45059, 44753, 44543, 44457, 44039, 43587, 43463, 43301, 42731, 42423, 42239, 41891, 41699, 41679, 41441, 41379, 41177, 40913, 40659, 40629, 40241, 39999, 39969, 39927, 39501, 39327, 39243, 39173, 38991, 38949, 38867, 38703, 38187, 38051, 38031, 37751, 37509, 37409, 37023, 36953, 35997, 35897, 35603, 35339, 35219, 35217, 35043, 34949, 34757, 34643, 34461, 33591, 33473, 33329, 33201, 33131, 32991, 32889, 32469, 31859, 31781, 31559, 31101, 31013, 30759, 30677, 29927, 29891, 29709, 29631, 29501, 29447, 28539, 28391, 28379, 27933, 27929, 27911, 27627, 27191, 26963, 26853, 26481, 26427, 26183, 26127, 26013, 26007, 25881, 25713, 25637, 25277, 25247, 24543, 23733, 22577, 22517, 22437, 22293, 22109, 22079, 21761, 21393, 21189, 20861, 20781, 20697, 20639, 20609, 20349, 20019, 19967, 19743, 19407, 19341, 19227, 18683, 18423, 18081, 18023, 17771, 17739, 17379, 17367, 16581, 16541, 16323, 15921, 15777, 15693, 15477, 15471, 15267, 15207, 15189, 14987, 14967, 14883, 14783, 14751, 14027, 13713, 13427]

/-- P0037 page 213, Table 1. The corresponding fixed candidate list. -/
def qs : List ℕ := offsets.map (fun d => 10 ^ 100 - d)

/-- P0037 page 213, row 10^100, printed list size 250.
The reconstructed list has exactly the permitted number of entries. -/
theorem length_eq : qs.length = 250 := by decide +kernel

/-- P0037 page 213, row 10^100, the printed outer candidate bound.
This checks only the finite integer data, not primality. -/
theorem offset_bounds : ∀ d ∈ offsets, d ≤ 68969 := by decide +kernel

/-- P0037 page 213. Every fixed candidate lies inside the sealed bounds. -/
theorem bounds : ∀ q ∈ qs, 10 ^ 100 - 68969 ≤ q ∧ q ≤ 10 ^ 100 := by
  intro q hq
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  have hb := offset_bounds d hd
  constructor <;> omega

/-- P0037 page 207, the recurrence at even offset zero.
A concrete small-prime witness shows the coverage leaf has an inhabited case.
This does not assert primality of any large candidate. -/
theorem offset_zero_instance : ∃ d ∈ offsets, d.Prime := by
  refine ⟨68501, by decide +kernel, ?_⟩
  norm_num


#print axioms length_eq
#print axioms offset_bounds
#print axioms bounds
#print axioms offset_zero_instance

end LeanLab.DtRS1998.Decomp372c
