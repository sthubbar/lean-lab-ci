/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
Chunk 1 of the short computer calculation behind Buthe 2014 display 4.6, upper half,
for 13209 ≤ N ≤ 30892: kernel check of the Legendre count at 113 checkpoints.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5MuMidS70

namespace LeanLab.BS2022GRH.Lemma5MuMidS70

/-- Checkpoints of chunk 1 after the first two. -/
def cpts1 : List ℕ := [13469, 13601, 13732, 13869, 14002, 14137, 14269, 14404, 14540, 14673, 14810, 14942, 15077, 15210, 15345, 15481, 15616, 15750, 15888, 16026, 16165, 16304, 16444, 16584, 16720, 16861, 16998, 17137, 17277, 17418, 17560, 17701, 17841, 17986, 18128, 18266, 18402, 18542, 18685, 18833, 18978, 19126, 19278, 19429, 19582, 19734, 19884, 20034, 20189, 20342, 20494, 20653, 20809, 20965, 21125, 21281, 21436, 21593, 21748, 21906, 22064, 22226, 22390, 22557, 22722, 22892, 23058, 23221, 23385, 23550, 23716, 23884, 24053, 24222, 24394, 24568, 24741, 24916, 25090, 25268, 25446, 25625, 25801, 25977, 26156, 26334, 26512, 26690, 26869, 27052, 27232, 27409, 27588, 27765, 27945, 28129, 28312, 28494, 28678, 28866, 29050, 29233, 29416, 29596, 29778, 29964, 30150, 30337, 30520, 30706, 30892]

theorem chk1 : chkC P (13209 :: 13336 :: cpts1) = true := by decide +kernel

theorem last1 : lastOf 13336 cpts1 = 30892 := by decide +kernel

/-- PROVED: Buthe 2014 display 4.6 upper half in integer form, `Q(N) ≤ 0.6079 N + 0.68 √N`,
for 13209 ≤ N ≤ 30892, by the kernel checked Legendre count. -/
theorem cover1 (N : ℕ) (h1 : 13209 ≤ N) (h2 : N ≤ 30892) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) :=
  chkC_sound P P_two_le P_sorted P_coprime cpts1 13209 13336 chk1 N h1 (last1 ▸ h2)

end LeanLab.BS2022GRH.Lemma5MuMidS70
