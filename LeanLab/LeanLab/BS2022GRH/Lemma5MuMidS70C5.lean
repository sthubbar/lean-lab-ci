/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
Chunk 5 of the short computer calculation behind Buthe 2014 display 4.6, upper half,
for 129489 ≤ N ≤ 177216: kernel check of the Legendre count at 113 checkpoints.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5MuMidS70

namespace LeanLab.BS2022GRH.Lemma5MuMidS70

/-- Checkpoints of chunk 5 after the first two. -/
def cpts5 : List ℕ := [130254, 130640, 131022, 131410, 131800, 132193, 132586, 132984, 133382, 133781, 134178, 134572, 134977, 135381, 135788, 136192, 136590, 136994, 137397, 137801, 138204, 138606, 139006, 139413, 139822, 140229, 140637, 141044, 141456, 141860, 142261, 142662, 143066, 143469, 143877, 144284, 144688, 145098, 145513, 145922, 146336, 146752, 147169, 147582, 147996, 148406, 148816, 149233, 149648, 150070, 150486, 150906, 151328, 151744, 152166, 152590, 153018, 153445, 153869, 154292, 154722, 155152, 155580, 156006, 156433, 156862, 157296, 157732, 158172, 158610, 159044, 159481, 159921, 160366, 160813, 161262, 161710, 162158, 162608, 163058, 163509, 163966, 164417, 164868, 165317, 165772, 166225, 166680, 167133, 167592, 168044, 168501, 168952, 169404, 169857, 170312, 170769, 171228, 171688, 172146, 172606, 173066, 173521, 173980, 174441, 174904, 175362, 175822, 176284, 176753, 177216]

theorem chk5 : chkC P (129489 :: 129872 :: cpts5) = true := by decide +kernel

theorem last5 : lastOf 129872 cpts5 = 177216 := by decide +kernel

/-- PROVED: Buthe 2014 display 4.6 upper half in integer form, `Q(N) ≤ 0.6079 N + 0.68 √N`,
for 129489 ≤ N ≤ 177216, by the kernel checked Legendre count. -/
theorem cover5 (N : ℕ) (h1 : 129489 ≤ N) (h2 : N ≤ 177216) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) :=
  chkC_sound P P_two_le P_sorted P_coprime cpts5 129489 129872 chk5 N h1 (last5 ▸ h2)

end LeanLab.BS2022GRH.Lemma5MuMidS70
