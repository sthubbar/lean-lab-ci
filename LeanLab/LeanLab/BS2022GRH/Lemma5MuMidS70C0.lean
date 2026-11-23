/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
Chunk 0 of the short computer calculation behind Buthe 2014 display 4.6, upper half,
for 3001 ≤ N ≤ 13209: kernel check of the Legendre count at 113 checkpoints.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5MuMidS70

namespace LeanLab.BS2022GRH.Lemma5MuMidS70

/-- Checkpoints of chunk 0 after the first two. -/
def cpts0 : List ℕ := [3116, 3170, 3229, 3289, 3346, 3404, 3460, 3520, 3582, 3645, 3708, 3778, 3845, 3912, 3980, 4048, 4117, 4186, 4257, 4325, 4394, 4465, 4536, 4609, 4681, 4754, 4826, 4896, 4968, 5038, 5116, 5194, 5276, 5358, 5440, 5521, 5608, 5694, 5782, 5868, 5956, 6044, 6129, 6213, 6298, 6385, 6473, 6557, 6644, 6733, 6818, 6910, 7004, 7096, 7192, 7286, 7381, 7476, 7570, 7662, 7754, 7845, 7938, 8033, 8129, 8222, 8316, 8413, 8510, 8605, 8704, 8798, 8893, 8996, 9096, 9194, 9290, 9390, 9490, 9594, 9696, 9796, 9898, 10001, 10109, 10213, 10320, 10425, 10536, 10645, 10758, 10870, 10985, 11101, 11218, 11340, 11461, 11580, 11700, 11821, 11945, 12069, 12192, 12314, 12438, 12565, 12696, 12822, 12953, 13081, 13209]

theorem chk0 : chkC P (3001 :: 3060 :: cpts0) = true := by decide +kernel

theorem last0 : lastOf 3060 cpts0 = 13209 := by decide +kernel

/-- PROVED: Buthe 2014 display 4.6 upper half in integer form, `Q(N) ≤ 0.6079 N + 0.68 √N`,
for 3001 ≤ N ≤ 13209, by the kernel checked Legendre count. -/
theorem cover0 (N : ℕ) (h1 : 3001 ≤ N) (h2 : N ≤ 13209) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) :=
  chkC_sound P P_two_le P_sorted P_coprime cpts0 3001 3060 chk0 N h1 (last0 ▸ h2)

end LeanLab.BS2022GRH.Lemma5MuMidS70
