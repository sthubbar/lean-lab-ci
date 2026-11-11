import LeanLab.HelfgottMajor.Decomp389b

/-!
Source checks and scalar prerequisites for the signed sampling leaves.
Source book Part IV pages 431 to 434, Lemma 16.9 and display 16.26.
These checks do not refute the sealed Gaussian sampling inequality.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Sampling431
open Real MeasureTheory Set Filter
open scoped Topology

/-- A hard cutoff with a nonzero retained endpoint is not continuous at that endpoint.
This audits the continuity hypothesis of Lemma 16.9 in its page 433 application.
It is a general cutoff check, not a counterexample to the Gaussian zero bound.
-/
theorem cutoff_not_continuous (f : ℝ → ℝ) (T : ℝ) (hf : f T ≠ 0) :
    ¬ContinuousAt (fun t : ℝ => if t ≤ T then f t else 0) T := by
  intro hc
  have hleft := hc.tendsto.mono_left (show 𝓝[>] T ≤ 𝓝 T from nhdsWithin_le_nhds)
  have hright : Tendsto (fun t : ℝ => if t ≤ T then f t else 0) (𝓝[>] T) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_Ioi] at ht
    simp [not_le.mpr ht]
  have heq := tendsto_nhds_unique hleft hright
  simp only [le_refl, ite_true] at heq
  exact hf heq

/-- The square of the printed zero count error envelope is not integrable to infinity.
This audits the infinite upper limit printed in book display 16.26.
The later page 434 estimate instead integrates only up to T0.
-/
theorem error_envelope_square_not_integrable :
    ¬IntegrableOn (fun t : ℝ => (0.15 * log t + 3.389) ^ 2) (Ioi 1) := by
  intro hi
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 1) := by
    apply hi.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hl : 0 ≤ log t := log_nonneg (le_of_lt ht)
    norm_num only [norm_one]
    nlinarith [sq_nonneg (0.15 * log t + 3.389)]
  have hh : ‖(1 : ℝ)‖ₑ = 0 ∨ volume (Ioi (1 : ℝ)) < ⊤ :=
    (integrableOn_const_iff (C := (1 : ℝ))).mp hconst
  simpa using hh

/-- The scalar antiderivative used for both squared logarithmic weights on book page 434.
This checks only the elementary calculus in the sampling proof.
-/
theorem hasDerivAt_log_weight_primitive (a b q t : ℝ) (hq : 0 < q) (ht : 0 < t) :
    HasDerivAt
      (fun u : ℝ => u * ((a * log (q * u) + b) ^ 2 -
        2 * a * (a * log (q * u) + b) + 2 * a ^ 2))
      ((a * log (q * t) + b) ^ 2) t := by
  have hl := (Real.hasDerivAt_log (mul_ne_zero hq.ne' ht.ne')).comp t
    ((hasDerivAt_id t).const_mul q)
  have hw := (hl.const_mul a).add_const b
  have hp := (hasDerivAt_id t).mul
    (((hw.pow 2).sub (hw.const_mul (2 * a))).add_const (2 * a ^ 2))
  convert hp using 1
  · rfl
  · simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp
    ; ring

/-- Exact integral of the squared logarithmic weight from height 1 to T.
Source book page 434, the two elementary weight integrals in the sampling proof.
-/
theorem integral_log_weight_sq (a b q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T, (a * log (q * t) + b) ^ 2) =
      T * ((a * log (q * T) + b) ^ 2 - 2 * a * (a * log (q * T) + b) + 2 * a ^ 2) -
      ((a * log q + b) ^ 2 - 2 * a * (a * log q + b) + 2 * a ^ 2) := by
  have hc : ContinuousOn (fun t : ℝ => (a * log (q * t) + b) ^ 2) (uIcc 1 T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    fun_prop (disch := positivity)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_log_weight_primitive a b q t hq
      (lt_of_lt_of_le zero_lt_one ((uIcc_of_le hT ▸ ht).1))) hc.intervalIntegrable
  simpa only [one_mul, mul_one] using hh

/-- Dropping the nonnegative lower endpoint gives the squared weight budget.
Source book page 434 before the square root estimates.
-/
theorem integral_log_weight_sq_le (a b q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T, (a * log (q * t) + b) ^ 2) ≤
      T * ((a * log (q * T) + b - a) ^ 2 + a ^ 2) := by
  rw [integral_log_weight_sq a b q T hq hT]
  nlinarith [sq_nonneg (a * log q + b - a), sq_nonneg a]

/-- The finite error envelope root has the coefficient 3.242 printed on book page 434.
This is only the scalar weight bound. It uses no zero count or Mellin value.
-/
theorem error_weight_root_bound (q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ q * T) :
    sqrt (∫ t in (1 : ℝ)..T, (0.15 * log (q * t) + 3.389) ^ 2) ≤
      (0.15 * log (q * T) + 3.242) * sqrt T := by
  have hT0 : 0 ≤ T := by linarith
  have hl := log_le_log (by positivity : (0 : ℝ) < 2 * π * exp 2) hlarge
  rw [log_mul (by positivity : (2 * π : ℝ) ≠ 0) (exp_ne_zero 2), log_exp] at hl
  have hlog : (3.5 : ℝ) ≤ log (q * T) := by linarith [log_two_pi_gt]
  have hcoef : (0.15 * log (q * T) + 3.389 - 0.15) ^ 2 + 0.15 ^ 2 ≤
      (0.15 * log (q * T) + 3.242) ^ 2 := by nlinarith
  have hbudget := (integral_log_weight_sq_le 0.15 3.389 q T hq hT).trans
    (mul_le_mul_of_nonneg_left hcoef hT0)
  apply (sqrt_le_iff).mpr
  refine ⟨mul_nonneg (by linarith) (sqrt_nonneg T), ?_⟩
  simpa only [mul_pow, sq_sqrt hT0, mul_comm] using hbudget

/-- The main logarithmic weight has the shifted logarithm budget on book page 434.
This is the scalar square root estimate before display 16.26.
-/
theorem main_weight_root_bound (q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ q * T) :
    sqrt (∫ t in (1 : ℝ)..T, log (q * t / (2 * π)) ^ 2) ≤
      sqrt T * log (q * T / (2 * π * sqrt (exp 1))) := by
  have hT0 : 0 ≤ T := by linarith
  have hqT0 : 0 < q * T := mul_pos hq (by linarith)
  have hl := log_le_log (by positivity : (0 : ℝ) < 2 * π * exp 2) hlarge
  rw [log_mul (by positivity : (2 * π : ℝ) ≠ 0) (exp_ne_zero 2), log_exp] at hl
  have hL : (2 : ℝ) ≤ log (q * T) - log (2 * π) := by linarith
  have hshift : log (q * T / (2 * π * sqrt (exp 1))) =
      log (q * T) - log (2 * π) - 1 / 2 := by
    rw [log_div hqT0.ne' (by positivity),
      log_mul (by positivity : (2 * π : ℝ) ≠ 0) (by positivity : sqrt (exp 1) ≠ 0),
      log_sqrt (exp_pos 1).le, log_exp]
    ring
  have heq : (∫ t in (1 : ℝ)..T, log (q * t / (2 * π)) ^ 2) =
      ∫ t in (1 : ℝ)..T, (1 * log (q * t) + -log (2 * π)) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    dsimp only
    rw [log_div (mul_ne_zero hq.ne' (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
      (by positivity)]
    ring
  have hcoef : (1 * log (q * T) + -log (2 * π) - 1) ^ 2 + 1 ^ 2 ≤
      (log (q * T) - log (2 * π) - 1 / 2) ^ 2 := by nlinarith
  have hbudget := (integral_log_weight_sq_le 1 (-log (2 * π)) q T hq hT).trans
    (mul_le_mul_of_nonneg_left hcoef hT0)
  rw [heq, hshift]
  apply (sqrt_le_iff).mpr
  refine ⟨mul_nonneg (sqrt_nonneg T) (by linarith), ?_⟩
  simpa only [mul_pow, sq_sqrt hT0] using hbudget

end LeanLab.HelfgottMajor.Sampling431
