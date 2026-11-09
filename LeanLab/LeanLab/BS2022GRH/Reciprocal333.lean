/- AI wrote the Lean code for CODEX task333. Goldbach is open.
Schoenfeld Corollary 2 p. 340 on the prime count range.
Source https://doi.org/10.1090/S0025-5718-1976-0457374-X. -/
import LeanLab.BS2022GRH.PrimeAbel333

namespace LeanLab.BS2022GRH.Reciprocal333
open Real Finset MeasureTheory intervalIntegral Filter Topology PrimeAbel333

/-- The sharp reciprocal upper bound follows from the prime count error alone
on its large endpoint range. Schoenfeld p. 340 display 6.21.
CONDITIONAL ON the explicit Lemma1J input and RH. -/
theorem reciprocal_upper_of_prime_count (h1 : PaperInputs148.Lemma1J)
    (hRH : RiemannHypothesis) (x : ℝ) (hx : 2657 ≤ x) :
    reciprocalSum x ≤ log (log x) + DecompC169c.mertensConstant +
      (3 * log x + 4) / (8 * π * √x) := by
  have hx0 : 0 < x := by linarith
  have hstep (y : ℝ) (hxy : x ≤ y) :
      reciprocalSum x ≤ reciprocalSum y - log (log y) + log (log x) +
        (3 * log x + 4) / (8 * π * √x) := by
    have hy : 2657 ≤ y := hx.trans hxy
    have hy0 : 0 < y := by linarith
    have hx2 : 2 < x := by linarith
    have hid := reciprocal_error_identity x y hx2 hxy
    have hEx : primeError x / x ≤ log x / (8 * π * √x) := by
      have h := div_le_div_of_nonneg_right (abs_le.mp (h1 hRH x hx)).2 hx0.le
      change primeError x / x ≤ _ at h
      convert h using 1
      have hs : √x ≠ 0 := (sqrt_pos.mpr hx0).ne'
      field_simp
      rw [sq_sqrt hx0.le]
    have hEy : -(primeError y / y) ≤ log y / (8 * π * √y) := by
      have he : -primeError y ≤ √y * log y / (8 * π) := by
        have h := (abs_le.mp (h1 hRH y hy)).1
        dsimp [primeError]
        linarith
      have h := div_le_div_of_nonneg_right he hy0.le
      rw [neg_div] at h
      convert h using 1
      have hs : √y ≠ 0 := (sqrt_pos.mpr hy0).ne'
      field_simp
      rw [sq_sqrt hy0.le]
    have hi : IntervalIntegrable (fun t : ℝ => primeError t / t ^ 2) volume x y := by
      convert (prime_weight_integrable x y (by linarith) hxy).sub
        (li_weight_integrable x y hx2 hxy) using 1
      ext t
      dsimp [primeError]
      ring
    have hj : IntervalIntegrable (fun t : ℝ => (log t / (t * √t)) / (8 * π)) volume x y := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [Set.uIcc_of_le hxy] at ht
      have ht0 : 0 < t := hx0.trans_le ht.1
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
    have hJ := integral_mono_on hxy hi.neg hj (fun t ht => by
      have ht0 : 0 < t := hx0.trans_le ht.1
      have ht : 2657 ≤ t := hx.trans ht.1
      have he : -primeError t ≤ √t * log t / (8 * π) := by
        have h := (abs_le.mp (h1 hRH t ht)).1
        dsimp [primeError]
        linarith
      calc
        -(primeError t / t ^ 2) = -primeError t / t ^ 2 := by ring
        _ ≤ (√t * log t / (8 * π)) / t ^ 2 :=
          div_le_div_of_nonneg_right he (sq_nonneg _)
        _ = (log t / (t * √t)) / (8 * π) := by
          have hs : √t ≠ 0 := (sqrt_pos.mpr ht0).ne'
          field_simp
          rw [sq_sqrt ht0.le]
          <;> ring)
    change (∫ t in x..y, -(primeError t / t ^ 2)) ≤
      (∫ t in x..y, (log t / (t * √t)) / (8 * π)) at hJ
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_div, kernel_integral x y (by linarith) hxy] at hJ
    have halg : log x / (8 * π * √x) + log y / (8 * π * √y) +
        ((2 * log x + 4) / √x - (2 * log y + 4) / √y) / (8 * π) =
        (3 * log x + 4) / (8 * π * √x) - (log y + 4) / (8 * π * √y) := by
      field_simp
      <;> ring
    have hlast : 0 ≤ (log y + 4) / (8 * π * √y) := by
      have hlog : 0 ≤ log y := log_nonneg (by linarith)
      positivity
    linarith
  have hlim := DecompC169c.reciprocal_limit
  change Tendsto (fun y : ℝ => reciprocalSum y - log (log y)) atTop
    (nhds DecompC169c.mertensConstant) at hlim
  have hlim' := hlim.add_const (log (log x) + (3 * log x + 4) / (8 * π * √x))
  have hres : reciprocalSum x ≤ DecompC169c.mertensConstant +
      (log (log x) + (3 * log x + 4) / (8 * π * √x)) := by
    apply ge_of_tendsto hlim'
    filter_upwards [eventually_ge_atTop x] with y hy
    convert hstep y hy using 1 <;> ring
  linarith

end LeanLab.BS2022GRH.Reciprocal333

#print axioms LeanLab.BS2022GRH.Reciprocal333.reciprocal_upper_of_prime_count
