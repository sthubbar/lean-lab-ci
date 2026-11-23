/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
Chunk 4 of the short computer calculation behind Buthe 2014 display 4.6, upper half,
for 89481 ≤ N ≤ 129489: kernel check of the Legendre count at 113 checkpoints.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5MuMidS70

namespace LeanLab.BS2022GRH.Lemma5MuMidS70

/-- Checkpoints of chunk 4 after the first two. -/
def cpts4 : List ℕ := [90137, 90468, 90801, 91128, 91453, 91785, 92117, 92446, 92773, 93098, 93425, 93756, 94081, 94408, 94738, 95069, 95400, 95730, 96064, 96402, 96742, 97085, 97426, 97768, 98110, 98456, 98798, 99145, 99490, 99830, 100172, 100514, 100854, 101196, 101534, 101877, 102217, 102558, 102898, 103244, 103594, 103948, 104297, 104648, 104998, 105348, 105694, 106041, 106393, 106738, 107088, 107437, 107782, 108129, 108473, 108821, 109170, 109525, 109881, 110236, 110589, 110944, 111301, 111657, 112014, 112368, 112729, 113094, 113460, 113828, 114193, 114556, 114925, 115293, 115660, 116029, 116402, 116781, 117160, 117540, 117920, 118305, 118689, 119073, 119464, 119850, 120236, 120621, 121006, 121392, 121781, 122173, 122568, 122962, 123356, 123744, 124130, 124512, 124893, 125277, 125661, 126050, 126434, 126816, 127197, 127577, 127960, 128342, 128720, 129102, 129489]

theorem chk4 : chkC P (89481 :: 89806 :: cpts4) = true := by decide +kernel

theorem last4 : lastOf 89806 cpts4 = 129489 := by decide +kernel

/-- PROVED: Buthe 2014 display 4.6 upper half in integer form, `Q(N) ≤ 0.6079 N + 0.68 √N`,
for 89481 ≤ N ≤ 129489, by the kernel checked Legendre count. -/
theorem cover4 (N : ℕ) (h1 : 89481 ≤ N) (h2 : N ≤ 129489) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) :=
  chkC_sound P P_two_le P_sorted P_coprime cpts4 89481 89806 chk4 N h1 (last4 ▸ h2)

end LeanLab.BS2022GRH.Lemma5MuMidS70
