/-
Elementary parameter choices in PP1993 page 48 display 26.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
These supporting facts use no analytic input.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp279b

namespace LeanLab.Languasco2004.Decomp489c
open Real Decomp279b
noncomputable section

/-- Page 48 display 26 and page 43 choice of B: the logarithmic margin.
The localization exponent is retained because L is log N, not log Y. -/
theorem parameter_margin {η A : ℝ} (hη : 0 < η) (hA : 0 < A) :
    2 * arcExponent η A * (η / 3) * (7 / 12 + η) ≥ 2 * A + 23 := by
  have heq : 2 * arcExponent η A * (η / 3) = 2 * (2 * A + 25) := by
    unfold arcExponent
    field_simp
  rw [heq]
  nlinarith [mul_pos hη (show 0 < 2 * A + 25 by linarith)]

/-- Page 48 display 26: each value under the supremum has enough saving.
This is the exact composed localization choice used by the sealed target. -/
theorem density_power_saving {N η A σ : ℝ}
    (hN : Real.exp 1 ≤ N) (hη : 0 < η) (hA : 0 < A)
    (hσ : σ ≤ 1 - 2 * arcExponent η A * Real.log (Real.log N) / Real.log N) :
    localization N η ^ (1 - η / 3 * (1 - σ)) ≤
      localization N η / Real.log N ^ (2 * A + 23) := by
  have hN0 : 0 < N := (Real.exp_pos 1).trans_le hN
  have hL : 1 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 1) hN
    simpa only [Real.log_exp] using this
  have hL0 : 0 < Real.log N := by linarith
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hL
  have hY : 0 < localization N η := Real.rpow_pos_of_pos hN0 _
  have hlogY : Real.log (localization N η) = (7 / 12 + η) * Real.log N := by
    rw [localization, Real.log_rpow hN0]
  have hs : 2 * arcExponent η A * Real.log (Real.log N) ≤ (1 - σ) * Real.log N := by
    have : 2 * arcExponent η A * Real.log (Real.log N) / Real.log N ≤ 1 - σ := by
      linarith
    exact (div_le_iff₀ hL0).mp this
  have hfactor : 0 ≤ η / 3 * (7 / 12 + η) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hs hfactor
  have hmargin := mul_le_mul_of_nonneg_right (parameter_margin hη hA) hll
  have hdecay : (2 * A + 23) * Real.log (Real.log N) ≤
      η / 3 * (1 - σ) * Real.log (localization N η) := by
    rw [hlogY]
    nlinarith [hmul, hmargin]
  rw [Real.rpow_def_of_pos hY, Real.rpow_def_of_pos hL0]
  rw [← Real.exp_log hY, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  rw [Real.log_exp]
  nlinarith [hdecay]

/-- Page 48 display 26: multiplying the supremum bound by L to 20
changes the logarithmic saving 2A plus 23 to 2A plus 3. -/
theorem log_power_cancellation {L Y A : ℝ} (hL : 0 < L) :
    L ^ (20 : ℕ) * (Y / L ^ (2 * A + 23)) = Y / L ^ (2 * A + 3) := by
  have heq : L ^ (2 * A + 23) = L ^ (20 : ℕ) * L ^ (2 * A + 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL]
    congr 1
    ring
  rw [heq]
  field_simp

#print axioms parameter_margin
#print axioms density_power_saving
#print axioms log_power_cancellation
end
end LeanLab.Languasco2004.Decomp489c
