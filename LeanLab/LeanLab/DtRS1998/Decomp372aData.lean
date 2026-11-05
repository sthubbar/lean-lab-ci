/-
AI wrote this Lean code for CODEX task372.
P0037 pages 207, 211 and 213. Fixed row 90 small-complement checks.
This file asserts no primality of any large candidate.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.Decomp372a

set_option maxRecDepth 100000

/-- P0037 pages 211 and 213. Reconstructed offsets for the first 209
candidates in increasing candidate order from 10^90 - 65981.
This finite data definition asserts no primality or exact prime index. -/
def offsets : List ℕ := [65981, 65867, 65799, 65631, 65237, 64931, 64907, 64581, 64409, 64349, 64253, 63839, 63459, 63261, 63161, 63047, 62961, 62759, 62429, 62279, 61833, 61781, 61479, 60863, 60849, 60813, 60749, 60693, 60669, 60461, 60093, 60077, 59871, 59771, 59513, 58889, 58827, 58809, 58799, 58701, 58637, 58247, 57699, 57579, 57563, 57299, 57269, 57231, 56817, 56699, 56597, 56073, 56033, 55911, 55487, 55389, 55377, 55313, 55149, 54423, 53673, 53669, 53583, 53279, 53003, 52457, 52371, 52307, 52239, 52211, 52167, 51777, 51629, 51441, 51407, 51401, 51081, 50867, 50609, 50459, 50151, 50049, 49991, 49949, 49223, 49079, 48941, 48867, 48591, 48431, 48107, 47723, 47219, 46841, 46587, 46521, 46373, 45983, 45971, 45887, 45177, 44519, 44343, 44183, 44159, 44091, 43893, 43749, 43721, 43719, 43521, 43307, 42609, 42531, 42521, 42297, 41843, 41297, 41103, 41061, 40809, 40607, 40499, 39291, 39273, 39213, 39101, 39059, 38973, 38883, 38829, 37977, 37817, 37343, 37047, 36761, 36159, 36083, 35747, 35511, 35397, 35357, 35331, 35291, 34773, 34727, 34571, 34103, 33863, 33443, 33269, 33191, 32447, 32361, 32123, 32039, 31269, 30861, 30261, 29969, 29753, 29483, 29397, 29369, 29313, 28937, 28811, 28709, 28457, 28187, 28131, 27807, 26931, 26649, 26613, 26501, 26421, 25967, 25707, 25167, 25163, 25113, 25079, 24563, 24167, 23627, 23489, 23111, 22811, 22451, 22229, 21947, 21317, 20927, 20877, 20841, 20471, 20057, 19809, 19707, 19089, 19049, 19011, 18927, 18777, 18563, 18303, 18231, 18087]

/-- P0037 page 213, Table 1. The corresponding fixed candidate list. -/
def qs : List ℕ := offsets.map (fun d => 10 ^ 90 - d)

/-- P0037 page 213, row 10^90, printed list size 209.
The reconstructed list has exactly the permitted number of entries. -/
theorem length_eq : qs.length = 209 := by decide +kernel

/-- P0037 page 213, row 10^90, the printed outer candidate bound.
This checks only the finite integer data, not primality. -/
theorem offset_bounds : ∀ d ∈ offsets, d ≤ 65981 := by decide +kernel

/-- P0037 page 213. Every fixed candidate lies inside the sealed bounds. -/
theorem bounds : ∀ q ∈ qs, 10 ^ 90 - 65981 ≤ q ∧ q ≤ 10 ^ 90 := by
  intro q hq
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  have hb := offset_bounds d hd
  constructor <;> omega

/-- P0037 page 207, the recurrence at even offset zero.
A concrete small-prime witness shows the coverage leaf has an inhabited case.
This does not assert primality of any large candidate. -/
theorem offset_zero_instance : ∃ d ∈ offsets, d.Prime := by
  refine ⟨65981, by decide +kernel, ?_⟩
  norm_num


#print axioms length_eq
#print axioms offset_bounds
#print axioms bounds
#print axioms offset_zero_instance

end LeanLab.DtRS1998.Decomp372a
