/-
AI wrote this Lean code. Codex task69, 2026-10-25.
The GRH remainder estimate 2.9 separated from the elementary Case 2 arithmetic.
Source: pages 347 to 348. This does not assert the global Dirichlet arc covering.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.MinorArithmetic
import LeanLab.Zinoviev1997.Series

namespace LeanLab.Zinoviev1997
open Real Finset

/-- The coordinate x from page 344. -/
noncomputable def minorCoordinate (N z : ℝ) : ℂ :=
  ((1 / N : ℝ) : ℂ) + ((2 * Real.pi * z : ℝ) : ℂ) * Complex.I

/-- The two alternatives in display 2.9 with their phase ranges.
This remains a cited GRH input. -/
def Lemma29At (N : ℝ) (q : ℕ) (z : ℝ) (s : ℂ) : Prop :=
  (2 * Real.pi * N * |z| ≤ 10 → ‖s‖ ≤
    1 / ((Nat.totient q : ℝ) * ‖minorCoordinate N z‖) +
      2.75 * Real.sqrt (N * q) * Real.log N) ∧
  (10 < 2 * Real.pi * N * |z| → ‖s‖ ≤
    1 / ((Nat.totient q : ℝ) * ‖minorCoordinate N z‖) +
      7 * N / Real.sqrt (4900 * Real.log N ^ 4) * Real.log N)

theorem minorCoordinate_real (N z : ℝ) : (minorCoordinate N z).re = 1 / N := by
  simp [minorCoordinate]

theorem minorCoordinate_imag (N z : ℝ) :
    |(minorCoordinate N z).im| = 2 * Real.pi * |z| := by
  simp [minorCoordinate, abs_mul, abs_of_pos Real.pi_pos]

theorem minorCoordinate_norm_real (N z : ℝ) (hN : 0 < N) :
    1 / N ≤ ‖minorCoordinate N z‖ := by
  have h := Complex.abs_re_le_norm (minorCoordinate N z)
  rw [minorCoordinate_real, abs_of_pos (by positivity : 0 < 1 / N)] at h
  exact h

theorem minorCoordinate_norm_phase (N z : ℝ) :
    2 * Real.pi * |z| ≤ ‖minorCoordinate N z‖ := by
  have h := Complex.abs_im_le_norm (minorCoordinate N z)
  rwa [minorCoordinate_imag] at h

/-- The lower error term of display 2.9 is exactly 0.1 N divided by log N. -/
theorem minor_lower_error (N : ℝ) (hN : 1 < N) :
    7 * N / Real.sqrt (4900 * Real.log N ^ 4) * Real.log N =
      0.1 * N / Real.log N := by
  have hl : 0 < Real.log N := Real.log_pos hN
  have he : Real.sqrt (4900 * Real.log N ^ 4) = 70 * Real.log N ^ 2 := by
    rw [show 4900 * Real.log N ^ 4 = (70 * Real.log N ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [he]
  field_simp
  ring

/-- Lemma 2.1 Case 2, CONDITIONAL ON only the pointwise GRH estimate 2.9.
The denominator and phase arithmetic are proved here. -/
theorem lemma21_case2_of_29 (N : ℝ) (q : ℕ) (z : ℝ) (s : ℂ)
    (hN : 10 ^ 20 ≤ N) (hq : Real.log N ^ 2 ≤ q)
    (hqτ : (q : ℝ) ≤ 4900 * Real.log N ^ 4) (h29 : Lemma29At N q z s) :
    ‖s‖ < 0.18 * N / Real.log N := by
  have hn : 0 < N := by linarith
  have hl : 46 ≤ Real.log N := le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  have hφ := totient_ge_six q (Real.log N) hl hq
  have hφ0 : (0 : ℝ) < Nat.totient q := by linarith
  have hx0 : 0 < ‖minorCoordinate N z‖ :=
    lt_of_lt_of_le (by positivity) (minorCoordinate_norm_real N z hn)
  by_cases hp : 2 * Real.pi * N * |z| ≤ 10
  · have hlead : 1 / ((Nat.totient q : ℝ) * ‖minorCoordinate N z‖) ≤ N / Nat.totient q := by
      rw [div_le_div_iff₀ (by positivity) hφ0]
      have hh := mul_le_mul_of_nonneg_left (minorCoordinate_norm_real N z hn) hn.le
      have he : N * (1 / N) = 1 := by field_simp
      rw [he] at hh
      have hm := mul_le_mul_of_nonneg_left hh hφ0.le
      nlinarith
    exact lt_of_le_of_lt (le_trans (h29.1 hp) (add_le_add hlead le_rfl))
      (minor_upper_case2 N q hN hq hqτ)
  · have hp' : 10 < 2 * Real.pi * N * |z| := lt_of_not_ge hp
    have hphase : 10 / N ≤ ‖minorCoordinate N z‖ := by
      rw [div_le_iff₀ hn]
      have hh := mul_le_mul_of_nonneg_left (minorCoordinate_norm_phase N z) hn.le
      nlinarith
    have hlead : 1 / ((Nat.totient q : ℝ) * ‖minorCoordinate N z‖) ≤
        N / (10 * Nat.totient q) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hh := mul_le_mul_of_nonneg_left hphase (show 0 ≤ N * Nat.totient q by positivity)
      have he : (N * Nat.totient q) * (10 / N) = 10 * Nat.totient q := by field_simp
      rw [he] at hh
      nlinarith
    have hs := h29.2 hp'
    rw [minor_lower_error N (by linarith)] at hs
    exact lt_of_le_of_lt (le_trans hs (add_le_add hlead le_rfl))
      (minor_lower_case2 N q hN hq)

end LeanLab.Zinoviev1997
