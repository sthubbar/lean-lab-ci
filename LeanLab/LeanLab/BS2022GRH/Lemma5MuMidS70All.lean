/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
Buthe 2014 display 4.6, upper half, on the middle range 3001 ≤ x < 438653, the short
computer calculation of Buthe's proof, assembled from the ten kernel checked chunks.
This is the statement of the LEAF `buthe_compute_mid` of Lemma5MuS63 with `K0 + 1 = 3001`.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5Coeffs138
import LeanLab.BS2022GRH.Lemma5MuMidS70C0
import LeanLab.BS2022GRH.Lemma5MuMidS70C1
import LeanLab.BS2022GRH.Lemma5MuMidS70C2
import LeanLab.BS2022GRH.Lemma5MuMidS70C3
import LeanLab.BS2022GRH.Lemma5MuMidS70C4
import LeanLab.BS2022GRH.Lemma5MuMidS70C5
import LeanLab.BS2022GRH.Lemma5MuMidS70C6
import LeanLab.BS2022GRH.Lemma5MuMidS70C7
import LeanLab.BS2022GRH.Lemma5MuMidS70C8
import LeanLab.BS2022GRH.Lemma5MuMidS70C9

namespace LeanLab.BS2022GRH.Lemma5MuMidS70
open Real Finset

/-- PROVED: `Q(N) ≤ 0.6079 N + 0.68 √N` for every integer `3001 ≤ N ≤ 438652`. -/
theorem nat_mid (N : ℕ) (h1 : 3001 ≤ N) (h2 : N ≤ 438652) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) := by
  rcases le_or_gt N 13209 with h0 | h0
  · exact cover0 N (by omega) h0
  rcases le_or_gt N 30892 with h1 | h1
  · exact cover1 N (by omega) h1
  rcases le_or_gt N 56156 with h2 | h2
  · exact cover2 N (by omega) h2
  rcases le_or_gt N 89481 with h3 | h3
  · exact cover3 N (by omega) h3
  rcases le_or_gt N 129489 with h4 | h4
  · exact cover4 N (by omega) h4
  rcases le_or_gt N 177216 with h5 | h5
  · exact cover5 N (by omega) h5
  rcases le_or_gt N 232825 with h6 | h6
  · exact cover6 N (by omega) h6
  rcases le_or_gt N 295556 with h7 | h7
  · exact cover7 N (by omega) h7
  rcases le_or_gt N 363858 with h8 | h8
  · exact cover8 N (by omega) h8
  exact cover9 N (by omega) (by omega)

theorem six_div_pi_sq_ge' : (0.6079 : ℝ) ≤ 6 / π ^ 2 := by
  have hp : π < 3.1416 := Real.pi_lt_d4
  have hp0 : 0 < π := Real.pi_pos
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem mMu_mul' (x : ℝ) (hx : 0 < x) :
    Lemma5Coeffs138.mMu x * x = 6 / π ^ 2 * x + 0.68 * √x := by
  unfold Lemma5Coeffs138.mMu
  have hs : 0 < √x := Real.sqrt_pos.2 hx
  have h3 : √x ^ 2 = x := Real.sq_sqrt hx.le
  field_simp
  linear_combination (-(17 / 25) * π ^ 2) * h3

/-- PROVED: Buthe 2014 display 4.6, upper half, for real `3001 ≤ x < 438653`, in the form
of journal Lemma 5. This is the LEAF `buthe_compute_mid` of Lemma5MuS63. -/
theorem buthe_compute_mid_proved : ∀ x : ℝ, (3001 : ℝ) ≤ x → x < 438653 →
    (((Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n)).card : ℝ) ≤ Lemma5Coeffs138.mMu x * x := by
  intro x h1 h2
  have hx0 : 0 ≤ x := by linarith
  have hN1 : 3001 ≤ ⌊x⌋₊ := by
    rw [Nat.le_floor_iff hx0]; exact_mod_cast h1
  have hN2 : ⌊x⌋₊ ≤ 438652 := by
    have : ⌊x⌋₊ < 438653 := by rw [Nat.floor_lt hx0]; exact_mod_cast h2
    omega
  have hb := nat_mid ⌊x⌋₊ hN1 hN2
  rw [mMu_mul' x (by linarith)]
  have h3 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have h4 : √(⌊x⌋₊ : ℝ) ≤ √x := Real.sqrt_le_sqrt h3
  have h5 := six_div_pi_sq_ge'
  have h6 : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg _
  have h7 : (S ⌊x⌋₊ : ℝ) = (((Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n)).card : ℝ) := rfl
  rw [← h7]
  nlinarith

end LeanLab.BS2022GRH.Lemma5MuMidS70
