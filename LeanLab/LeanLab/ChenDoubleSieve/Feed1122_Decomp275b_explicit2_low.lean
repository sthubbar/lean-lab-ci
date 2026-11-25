import Mathlib

/-!
Low piece of `leaf_explicit2` in `Feed1122_Decomp275b_values_explicit.lean`, for
Wu 2004, arXiv 0705.1652, page 39 equation 10.4 and the final display on page 42.
On the range from 258/125 to 3 the inner integral runs from 3 to max t 3 = 3, so it
vanishes and the integrand is 2 / t / of 1 - t/6. Its antiderivative is
2 log t minus 2 log of 6 - t, so the piece equals 2 log of 82/43, and the leaf
with its factor 4 gets 8 log of 82/43.
The logarithm is bounded by the Mathlib series remainder lemma
`Real.abs_log_sub_add_sum_range_le` at x = 39/82, since 82/43 = 1/(1 - 39/82).
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ChenDoubleSieve.Feed1122Explicit2Low

open Real Finset MeasureTheory intervalIntegral

/-- Upper bound for minus log of 1 - x from the Mathlib series remainder. -/
theorem neg_log_one_sub_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    -log (1 - x) ≤ (∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1)) + x ^ (n + 1) / (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).1
  linarith

/-- The log bound, within 1e-9 of the true value 0.6455191315707. -/
theorem log_82_43_le : log (82 / 43 : ℝ) ≤ 6455191325 / 10000000000 := by
  have he : log (82 / 43 : ℝ) = -log (1 - 39 / 82) := by
    rw [show (1 - 39 / 82 : ℝ) = (82 / 43)⁻¹ by norm_num, Real.log_inv]
    ring
  rw [he]
  refine le_trans (neg_log_one_sub_le (39 / 82) (by norm_num) (by norm_num) 28) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- Exact value of the elementary integral. -/
theorem integral_low :
    ∫ t in (258/125 : ℝ)..3, 2 / t / (1 - t / 6) = 2 * log (82 / 43) := by
  have hderiv : ∀ x ∈ Set.uIcc (258/125 : ℝ) 3,
      HasDerivAt (fun t => 2 * log t - 2 * log (6 - t)) (2 / x / (1 - x / 6)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h1, h2⟩ := hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at h1; norm_num at h1
    have hx6 : 6 - x ≠ 0 := by intro h; linarith
    have d1 := (Real.hasDerivAt_log hx0).const_mul 2
    have d2 := (((hasDerivAt_id x).const_sub 6).log hx6).const_mul 2
    have hx6' : 1 - x / 6 ≠ 0 := by intro h; linarith
    have e : 2 / x / (1 - x / 6) = 2 * x⁻¹ - 2 * (-1 / (6 - id x)) := by
      simp only [id]
      field_simp
      ring
    rw [e]
    exact d1.sub d2
  rw [integral_eq_sub_of_hasDerivAt hderiv]
  · have e1 : log (82 / 43 : ℝ) = log (492 / 125) - log (258 / 125) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    rw [e1]
    norm_num
    ring
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h1, h2⟩ := hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at h1; norm_num at h1
    have hx6' : 1 - x / 6 ≠ 0 := by intro h; linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)

/-- The leaf integrand restricted to the range from 258/125 to 3 equals 2 log of 82/43. -/
theorem leaf2_low_eq :
    (∫ t in (258/125 : ℝ)..3,
      (2 + 2 * ∫ s in (3:ℝ)..max t 3, Real.log (s - 2) / (s - 1)) / t / (1 - t / 6))
      = 2 * log (82 / 43) := by
  rw [← integral_low]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num)] at ht
  simp only [max_eq_right ht.2, intervalIntegral.integral_same, mul_zero, add_zero]

/-- The leaf piece with its factor 4 is exactly 8 log of 82/43. -/
theorem leaf2_low_eq8 :
    4 * (∫ t in (258/125 : ℝ)..3,
      (2 + 2 * ∫ s in (3:ℝ)..max t 3, Real.log (s - 2) / (s - 1)) / t / (1 - t / 6))
      = 8 * log (82 / 43) := by
  rw [leaf2_low_eq]; ring

/-- The leaf piece with its factor 4 is at most the rational bound 8 B. -/
theorem leaf2_low_le :
    4 * (∫ t in (258/125 : ℝ)..3,
      (2 + 2 * ∫ s in (3:ℝ)..max t 3, Real.log (s - 2) / (s - 1)) / t / (1 - t / 6))
      ≤ 8 * (6455191325 / 10000000000 : ℝ) := by
  rw [leaf2_low_eq8]
  have := log_82_43_le
  linarith

end LeanLab.ChenDoubleSieve.Feed1122Explicit2Low
