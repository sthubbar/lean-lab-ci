/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
Chunk 2 of the short computer calculation behind Buthe 2014 display 4.6, upper half,
for 30892 ≤ N ≤ 56156: kernel check of the Legendre count at 113 checkpoints.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5MuMidS70

namespace LeanLab.BS2022GRH.Lemma5MuMidS70

/-- Checkpoints of chunk 2 after the first two. -/
def cpts2 : List ℕ := [31277, 31473, 31672, 31870, 32072, 32277, 32481, 32685, 32893, 33097, 33304, 33508, 33712, 33912, 34112, 34314, 34521, 34728, 34932, 35140, 35353, 35565, 35780, 35989, 36200, 36408, 36618, 36829, 37042, 37257, 37473, 37697, 37921, 38138, 38358, 38578, 38805, 39033, 39260, 39488, 39721, 39956, 40189, 40421, 40648, 40882, 41114, 41352, 41585, 41816, 42045, 42276, 42505, 42732, 42960, 43186, 43410, 43633, 43860, 44085, 44312, 44541, 44764, 44993, 45221, 45446, 45673, 45898, 46125, 46352, 46578, 46801, 47022, 47245, 47466, 47692, 47916, 48142, 48377, 48609, 48845, 49078, 49314, 49552, 49792, 50032, 50266, 50504, 50740, 50978, 51217, 51457, 51698, 51937, 52178, 52422, 52668, 52913, 53161, 53406, 53656, 53902, 54153, 54400, 54650, 54897, 55144, 55389, 55641, 55896, 56156]

theorem chk2 : chkC P (30892 :: 31081 :: cpts2) = true := by decide +kernel

theorem last2 : lastOf 31081 cpts2 = 56156 := by decide +kernel

/-- PROVED: Buthe 2014 display 4.6 upper half in integer form, `Q(N) ≤ 0.6079 N + 0.68 √N`,
for 30892 ≤ N ≤ 56156, by the kernel checked Legendre count. -/
theorem cover2 (N : ℕ) (h1 : 30892 ≤ N) (h2 : N ≤ 56156) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) :=
  chkC_sound P P_two_le P_sorted P_coprime cpts2 30892 31081 chk2 N h1 (last2 ▸ h2)

end LeanLab.BS2022GRH.Lemma5MuMidS70
