/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
Chunk 3 of the short computer calculation behind Buthe 2014 display 4.6, upper half,
for 56156 ≤ N ≤ 89481: kernel check of the Legendre count at 113 checkpoints.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5MuMidS70

namespace LeanLab.BS2022GRH.Lemma5MuMidS70

/-- Checkpoints of chunk 3 after the first two. -/
def cpts3 : List ℕ := [56673, 56930, 57193, 57458, 57722, 57985, 58248, 58516, 58786, 59060, 59329, 59600, 59872, 60142, 60414, 60685, 60953, 61228, 61497, 61764, 62032, 62301, 62569, 62838, 63112, 63388, 63661, 63936, 64212, 64488, 64770, 65046, 65322, 65605, 65886, 66169, 66456, 66741, 67026, 67313, 67600, 67884, 68168, 68448, 68734, 69026, 69321, 69613, 69906, 70197, 70490, 70785, 71077, 71370, 71664, 71952, 72244, 72536, 72828, 73126, 73428, 73729, 74034, 74340, 74646, 74954, 75260, 75566, 75877, 76186, 76493, 76806, 77114, 77429, 77745, 78058, 78377, 78689, 79002, 79326, 79646, 79969, 80300, 80626, 80946, 81268, 81596, 81925, 82252, 82576, 82901, 83228, 83554, 83881, 84209, 84532, 84857, 85182, 85506, 85837, 86169, 86504, 86834, 87166, 87502, 87834, 88165, 88497, 88822, 89150, 89481]

theorem chk3 : chkC P (56156 :: 56414 :: cpts3) = true := by decide +kernel

theorem last3 : lastOf 56414 cpts3 = 89481 := by decide +kernel

/-- PROVED: Buthe 2014 display 4.6 upper half in integer form, `Q(N) ≤ 0.6079 N + 0.68 √N`,
for 56156 ≤ N ≤ 89481, by the kernel checked Legendre count. -/
theorem cover3 (N : ℕ) (h1 : 56156 ≤ N) (h2 : N ≤ 89481) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) :=
  chkC_sound P P_two_le P_sorted P_coprime cpts3 56156 56414 chk3 N h1 (last3 ▸ h2)

end LeanLab.BS2022GRH.Lemma5MuMidS70
