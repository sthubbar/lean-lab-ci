/-
AI wrote this Lean code for CODEX task372.
P0037 pages 207, 211 and 213. Fixed row 95 small-complement checks.
This file asserts no primality of any large candidate.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.Decomp372b

set_option maxRecDepth 100000

/-- P0037 pages 211 and 213. Reconstructed offsets for the first 207
candidates in increasing candidate order from 10^95 - 64011.
This finite data definition asserts no primality or exact prime index. -/
def offsets : List ℕ := [64011, 63671, 63209, 63003, 62927, 62801, 62771, 62763, 62607, 62471, 62411, 62343, 62093, 62009, 61067, 60567, 60533, 60437, 60407, 60179, 59909, 59877, 59741, 59523, 59507, 59273, 58971, 58689, 58251, 57719, 57299, 57281, 56777, 56667, 56609, 56559, 56063, 55961, 55469, 55419, 55107, 55047, 54677, 54659, 54653, 54651, 54441, 54299, 54263, 54183, 54173, 54057, 54051, 53741, 53609, 53549, 53493, 53367, 53207, 53199, 53039, 52961, 52881, 52401, 52373, 52053, 51893, 51753, 51659, 51533, 51353, 51351, 51339, 51279, 50823, 50813, 50789, 49883, 49667, 49659, 49451, 49373, 49127, 48869, 48623, 48441, 48033, 47991, 47811, 47747, 47679, 47379, 47291, 46719, 46619, 45989, 45867, 45749, 45747, 45639, 45597, 45411, 45389, 45047, 44891, 44829, 44699, 44669, 43851, 43833, 42851, 42623, 42617, 42471, 42333, 41229, 40859, 40791, 40757, 40653, 40503, 40403, 40307, 39977, 39861, 39749, 39717, 39473, 39417, 39167, 38661, 38637, 38513, 38429, 37979, 36873, 36731, 36347, 35417, 35337, 35283, 35259, 35141, 35129, 34923, 34653, 34563, 33777, 33627, 33581, 33191, 32969, 32967, 32963, 32787, 32321, 32157, 32103, 31851, 31493, 30893, 29903, 29561, 29469, 29361, 29229, 29199, 29183, 28983, 28821, 28559, 28013, 27623, 27189, 26909, 26781, 26757, 26627, 26613, 26327, 26093, 25481, 25281, 25137, 24723, 24549, 24521, 24489, 23967, 23907, 23883, 23381, 23171, 23111, 22959, 22943, 22733, 22443, 22317, 22313, 22101, 22067, 21843, 21743, 21717, 21221, 20937]

/-- P0037 page 213, Table 1. The corresponding fixed candidate list. -/
def qs : List ℕ := offsets.map (fun d => 10 ^ 95 - d)

/-- P0037 page 213, row 10^95, printed list size 207.
The reconstructed list has exactly the permitted number of entries. -/
theorem length_eq : qs.length = 207 := by decide +kernel

/-- P0037 page 213, row 10^95, the printed outer candidate bound.
This checks only the finite integer data, not primality. -/
theorem offset_bounds : ∀ d ∈ offsets, d ≤ 64011 := by decide +kernel

/-- P0037 page 213. Every fixed candidate lies inside the sealed bounds. -/
theorem bounds : ∀ q ∈ qs, 10 ^ 95 - 64011 ≤ q ∧ q ≤ 10 ^ 95 := by
  intro q hq
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  have hb := offset_bounds d hd
  constructor <;> omega

/-- P0037 page 207, the recurrence at even offset zero.
A concrete small-prime witness shows the coverage leaf has an inhabited case.
This does not assert primality of any large candidate. -/
theorem offset_zero_instance : ∃ d ∈ offsets, d.Prime := by
  refine ⟨63671, by decide +kernel, ?_⟩
  norm_num


#print axioms length_eq
#print axioms offset_bounds
#print axioms bounds
#print axioms offset_zero_instance

end LeanLab.DtRS1998.Decomp372b
