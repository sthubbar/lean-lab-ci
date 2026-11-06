import LeanLab.RamareSaouter2003.Circle419
import LeanLab.RamareSaouter2003.Decomp378c

/-!
Rosser 1941 p. 224 and Backlund pp. 361 to 374.
The original circle_gamma_bound splits into zeta growth on the circle,
a gamma remainder bound and a real integral budget.
The original target and the actual zeta center are unchanged.
The three source leaves are OPEN. Their assembly is CONDITIONAL ON them.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp419a
open Real Complex MeasureTheory Decomp359g Circle419

/-- LEAF. Rosser p. 224, the bounds on G from Backlund pp. 361 to 369.
Backlund display 54 bounds the right strip, display 56 the critical strip,
and display 77 the short left strip. The Dirichlet series bounds the far right.
The two heights are bounded separately by T plus the radius. -/
theorem zeta_circle_bound (T φ : ℝ) (hT : 1400 ≤ T) (hφ : φ ∈ Set.Icc (0 : ℝ) π) :
    ‖riemannZeta ((1.32 : ℂ) * Complex.exp (φ * I) + 5 / 4 + T * I)‖ ≤
      Real.exp (logEnvelope T φ) ∧
    ‖riemannZeta ((1.32 : ℂ) * Complex.exp (φ * I) + 5 / 4 - T * I)‖ ≤
      Real.exp (logEnvelope T φ) := by
  sorry

/-- LEAF. Backlund p. 374, the three final gamma remainder estimates.
Their sum is 1 over 3T plus 1 over 16T plus 1 over 8T, equal to 25 over 48T.
The gamma argument has the same continuous normalization as Rosser p. 224. -/
theorem gamma_remainder_bound (T : ℝ) (hT : 1400 ≤ T) :
    |gammaRemainder T| ≤ 25 / (48 * T) := by
  sorry

/-- LEAF. Backlund pp. 371 to 373, displays 82 and the real integral budget,
with Rosser p. 224 radius 1.32 and exact Euler product center cost.
Only a real piecewise envelope occurs. There are no powers or gamma functions.
The correction 217 over 48piT combines 4 over piT with 25 over 48piT. -/
theorem envelope_budget (T : ℝ) (hT : 1400 ≤ T) :
    (∫ φ in (0 : ℝ)..π, logEnvelope T φ) / (2 * π * Real.log (4 * 1.32 / 3)) +
      1 / 2 + 217 / (48 * π * T) ≤
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 +
        Real.log ‖riemannZeta (5 / 2) / riemannZeta (5 / 4)‖ /
          (2 * Real.log (4 * 1.32 / 3)) := by
  sorry

/-- Rosser p. 224, exactly the existing circle_gamma_bound statement.
CONDITIONAL ON zeta_circle_bound, gamma_remainder_bound and envelope_budget.
The averaged powers, integration and center comparison are proved. -/
theorem circle_gamma_bound (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) (N : ℕ) (hN : 0 < N) :
    (∫ φ in (0 : ℝ)..π,
      Real.log ‖poweredZeta T N ((1.32 : ℂ) * Complex.exp (φ * Complex.I))‖) /
        (2 * π * Real.log (4 * 1.32 / 3) * N) +
      1 / 2 + 4 / (π * T) + |gammaRemainder T| / π ≤
        0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ /
            (2 * Real.log (4 * 1.32 / 3)) := by
  have ht : 1400 ≤ T := hA.trans hT
  have hq : 0 < Real.log (4 * 1.32 / 3) := Real.log_pos (by norm_num)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 < 2 * π * Real.log (4 * 1.32 / 3) := by positivity
  have hi := intervalIntegral.integral_mono_on Real.pi_pos.le
    (powered_log_integrable T ht N) ((logEnvelope_integrable T).const_mul (N : ℝ))
    (fun φ hφ => by
      obtain ⟨hp, hm⟩ := zeta_circle_bound T φ ht hφ
      exact log_average_pow_le _ _ N _ (logEnvelope_nonneg T φ ht) hp hm)
  rw [intervalIntegral.integral_const_mul] at hi
  have hdiv := div_le_div_of_nonneg_right hi (mul_pos hden hNR).le
  have hcancel : ((N : ℝ) * ∫ φ in (0 : ℝ)..π, logEnvelope T φ) /
      (2 * π * Real.log (4 * 1.32 / 3) * N) =
      (∫ φ in (0 : ℝ)..π, logEnvelope T φ) /
        (2 * π * Real.log (4 * 1.32 / 3)) := by field_simp
  rw [hcancel] at hdiv
  have hc := center_euler_lower (5 / 4) T (by norm_num)
  norm_num only [show (2 : ℝ) * (5 / 4) = 5 / 2 by norm_num,
    Complex.ofReal_div, Complex.ofReal_ofNat] at hc
  have hcz : 0 < ‖riemannZeta (5 / 2) / riemannZeta (5 / 4)‖ := by
    apply norm_pos_iff.mpr
    exact div_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hlog := div_le_div_of_nonneg_right (Real.log_le_log hcz hc) (by positivity : 0 ≤ 2 * Real.log (4 * 1.32 / 3))
  have hg := div_le_div_of_nonneg_right (gamma_remainder_bound T ht) Real.pi_pos.le
  have hid : 4 / (π * T) + (25 / (48 * T)) / π = 217 / (48 * π * T) := by ring
  have hb := envelope_budget T ht
  rw [← hid] at hb
  linarith

end LeanLab.RamareSaouter2003.Decomp419a

#print axioms LeanLab.RamareSaouter2003.Decomp419a.zeta_circle_bound
#print axioms LeanLab.RamareSaouter2003.Decomp419a.gamma_remainder_bound
#print axioms LeanLab.RamareSaouter2003.Decomp419a.envelope_budget
#print axioms LeanLab.RamareSaouter2003.Decomp419a.circle_gamma_bound
