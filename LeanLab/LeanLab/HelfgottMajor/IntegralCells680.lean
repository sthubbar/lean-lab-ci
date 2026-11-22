import Mathlib

/-!
Rational cell bounds for the integral after P0014 display 4.12 on page 35.
Source https://arxiv.org/abs/1305.2897v4.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.IntegralCells680

/-- A rectangle bound using the upper endpoint in the logarithm and the lower endpoint
in the denominator. This avoids any assumption about convexity. -/
theorem cell_bound (a b ℓ C : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hl : Real.log (b ^ 2 + 9 / 4) ≤ ℓ)
    (hC : (b - a) * ℓ ^ 2 / (1 / 4 + a ^ 2) ≤ C) :
    ∫ τ in a..b, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ C := by
  have hc : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 /
      (1 / 4 + τ ^ 2)) :=
    Continuous.div (Continuous.pow (Continuous.log (by fun_prop)
      (fun τ => by positivity)) 2) (by fun_prop) (fun τ => by positivity)
  have hp : ∀ τ ∈ Set.Icc a b,
      Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤
        ℓ ^ 2 / (1 / 4 + a ^ 2) := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := ha.trans hτ.1
    have hsqa : a ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ ha hτ.1 2
    have hsqb : τ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hτ0 hτ.2 2
    have hlog0 : 0 ≤ Real.log (τ ^ 2 + 9 / 4) := Real.log_nonneg (by nlinarith [sq_nonneg τ])
    have hlog : Real.log (τ ^ 2 + 9 / 4) ≤ ℓ :=
      (Real.log_le_log (by positivity) (by linarith)).trans hl
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ hlog0 hlog 2)
      (by positivity) (by linarith)
  have hi := intervalIntegral.integral_mono_on hab (hc.intervalIntegrable a b)
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => ℓ ^ 2 / (1 / 4 + a ^ 2)) MeasureTheory.volume a b) hp
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  exact hi.trans (by simpa only [mul_div_assoc] using hC)

end LeanLab.HelfgottMajor.IntegralCells680
