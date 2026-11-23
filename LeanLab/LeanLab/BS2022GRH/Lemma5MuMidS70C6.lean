/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
Chunk 6 of the short computer calculation behind Buthe 2014 display 4.6, upper half,
for 177216 ≤ N ≤ 232825: kernel check of the Legendre count at 113 checkpoints.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5MuMidS70

namespace LeanLab.BS2022GRH.Lemma5MuMidS70

/-- Checkpoints of chunk 6 after the first two. -/
def cpts6 : List ℕ := [178144, 178608, 179073, 179541, 180012, 180482, 180948, 181416, 181882, 182342, 182808, 183273, 183745, 184213, 184678, 185137, 185600, 186062, 186526, 186994, 187464, 187938, 188410, 188888, 189366, 189841, 190320, 190794, 191269, 191750, 192229, 192706, 193188, 193676, 194168, 194661, 195148, 195630, 196122, 196617, 197113, 197609, 198110, 198610, 199109, 199604, 200101, 200596, 201096, 201596, 202101, 202601, 203100, 203598, 204094, 204586, 205078, 205572, 206069, 206570, 207077, 207581, 208090, 208594, 209100, 209602, 210110, 210614, 211120, 211620, 212118, 212622, 213129, 213642, 214153, 214662, 215172, 215676, 216181, 216686, 217198, 217712, 218229, 218745, 219264, 219778, 220294, 220813, 221329, 221844, 222364, 222886, 223410, 223932, 224448, 224966, 225480, 226004, 226525, 227040, 227561, 228085, 228604, 229122, 229648, 230173, 230704, 231234, 231765, 232300, 232825]

theorem chk6 : chkC P (177216 :: 177682 :: cpts6) = true := by decide +kernel

theorem last6 : lastOf 177682 cpts6 = 232825 := by decide +kernel

/-- PROVED: Buthe 2014 display 4.6 upper half in integer form, `Q(N) ≤ 0.6079 N + 0.68 √N`,
for 177216 ≤ N ≤ 232825, by the kernel checked Legendre count. -/
theorem cover6 (N : ℕ) (h1 : 177216 ≤ N) (h2 : N ≤ 232825) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) :=
  chkC_sound P P_two_le P_sorted P_coprime cpts6 177216 177682 chk6 N h1 (last6 ▸ h2)

end LeanLab.BS2022GRH.Lemma5MuMidS70
