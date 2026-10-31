/-
Tao 2012, P0007, unit U-0925, run 20261018T0803Z-19871. arXiv 1201.6656 v4, proof of
Proposition 8.3, read in Claude in Chrome, arxiv.org/html/1201.6656, 2026-10-18.

The error budget of Proposition 8.3, with the slips F-0015 to F-0017 corrected, and the
repair of F-0024. The proof splits the error of (8.12) into
* the `η₀` and `D` error, which the paper bounds by `10^{-3}`,
* (8.15) `10^{-6} x ∫_{|α| ≤ R} |S_{η₁,1}(x, α)| dα`, by Cauchy-Schwarz and Corollary 4.7,
* (8.16) `10^{-6} x² ∫_{|α| ≤ R} |η̂₁(αx)| dα`, by `|η̂₁(ξ)| ≤ min(‖η₁‖₁, 1/(π|ξ|))`,
* the convolution `∫ η₁(s) η₁(1 - s - t/K) ds = 2/3 + O*(10 · 0.7 / K)`, F-0017,
* the tail `|α| > R` of the main integral, by Lemma 3.3,
with `R = T₀/(3.6 π x)`. The analytic steps are the paper's and stay cited; this file proves
the arithmetic: each piece's numerical size, and that the pieces sum to at most 0.076, inside
the 0.09 that `Cor48.repair_margin` needs. So F-0024 is repaired CONDITIONAL ON the paper's
Corollary 4.7, Lemma 3.3, Lemma 4.3 and Proposition 7.2.

The (8.15) bound keeps the paper's factor `4 log 2`, larger than the `‖η₁‖₂² = 2/3` that
Corollary 4.7 gives for `η₁`, so it is an over-estimate; with 2/3 it is about 0.033.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.Tao2012.Prop83

open Real

noncomputable def T0 : ℝ := 3.29e9
noncomputable def K : ℝ := 1e3

/-- `U = T₀ / (3.6 π) = R x`. -/
noncomputable def U : ℝ := T0 / (3.6 * π)

theorem U_pos : 0 < U := by unfold U T0; have := pi_pos; positivity

theorem U_le : U ≤ 2.9105e8 := by
  unfold U T0
  have := pi_gt_d2
  rw [div_le_iff₀ (by positivity)]; nlinarith

theorem U_ge : 2.9e8 ≤ U := by
  unfold U T0
  have := pi_lt_d2
  rw [le_div_iff₀ (by positivity)]; nlinarith

theorem exp_one_lt' : exp 1 < 2.72 := by have := exp_one_lt_d9; linarith
theorem exp_one_gt' : 2.718 < exp 1 := by have := exp_one_gt_d9; linarith

/-- `log x ≥ 84` for `x ≥ 8.7e36`, from `e^84 < 2.72^84 < 8.7e36`. -/
theorem log_x_ge {x : ℝ} (hx : 8.7e36 ≤ x) : 84 ≤ log x := by
  have hx0 : 0 < x := by linarith
  rw [le_log_iff_exp_le hx0]
  have h1 : exp 1 ^ 84 ≤ (2.72 : ℝ) ^ 84 :=
    pow_le_pow_left₀ (exp_pos 1).le exp_one_lt'.le 84
  rw [← exp_nat_mul] at h1
  norm_num at h1
  have h2 : (2.72 : ℝ) ^ 84 ≤ 8.7e36 := by norm_num
  linarith

/-- `log (2U) ≤ 20.25`, from `e^{20.25} ≥ 2.718^20 · 1.25 > 5.83e8 ≥ 2U`. -/
theorem log_2U_le : log (2 * U) ≤ 20.25 := by
  have h2U : 0 < 2 * U := by have := U_pos; linarith
  rw [log_le_iff_le_exp h2U]
  have he : exp 20.25 = exp 1 ^ 20 * exp 0.25 := by
    rw [← exp_nat_mul, ← exp_add]; norm_num
  have h1 : (2.718 : ℝ) ^ 20 ≤ exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num) exp_one_gt'.le 20
  have h3 : (1.25 : ℝ) ≤ exp 0.25 := by
    have := add_one_le_exp (0.25 : ℝ); linarith
  have h4 : (5.83e8 : ℝ) ≤ 2.718 ^ 20 * 1.25 := by norm_num
  have h5 : 2.718 ^ 20 * 1.25 ≤ exp 1 ^ 20 * exp 0.25 :=
    mul_le_mul h1 h3 (by norm_num) (by positivity)
  have := U_le
  rw [he]; linarith

theorem log_2U_pos : 0 < log (2 * U) := log_pos (by have := U_ge; linarith)

/-- `2 / (1 - r) ≤ 2.6354` for `r = log (2U) / log x`, `x ≥ 8.7e36`. -/
theorem cor47_factor_le {x : ℝ} (hx : 8.7e36 ≤ x) :
    2 / (1 - log (2 * U) / log x) ≤ 2.6354 := by
  have hl := log_x_ge hx
  have hu := log_2U_le
  have hr : log (2 * U) / log x ≤ 20.25 / 84 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [log_2U_pos]
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- (8.15), with Cauchy-Schwarz over the interval of length `2R`: at most
`10^{-6} x √(2U · 2/(1 - r) · 4 log 2 · 1.04)`, which is at most `0.067 x`. -/
theorem eq815_le {x : ℝ} (hx : 8.7e36 ≤ x) :
    1e-6 * sqrt (2 * U * (2 / (1 - log (2 * U) / log x)) * (4 * log 2) * 1.04) ≤ 0.067 := by
  have hf := cor47_factor_le hx
  have hU := U_le
  have hU0 := U_pos
  have h2 := log_two_lt_d9
  have h2' := log_two_gt_d9
  have hf0 : 0 < 2 / (1 - log (2 * U) / log x) := by
    have hl := log_x_ge hx
    have hr : log (2 * U) / log x < 1 := by
      rw [div_lt_one (by linarith)]; linarith [log_2U_le]
    apply div_pos (by norm_num) (by linarith)
  have hQ : 2 * U * (2 / (1 - log (2 * U) / log x)) * (4 * log 2) * 1.04 ≤ 4.489e9 := by
    have a : 2 * U * (2 / (1 - log (2 * U) / log x)) ≤ 2 * 2.9105e8 * 2.6354 := by
      have := mul_le_mul (show 2 * U ≤ 2 * 2.9105e8 by linarith) hf hf0.le (by norm_num)
      linarith
    have b : 4 * log 2 * 1.04 ≤ 4 * 0.6931471808 * 1.04 := by nlinarith
    have hpos : 0 ≤ 2 * U * (2 / (1 - log (2 * U) / log x)) := by positivity
    calc 2 * U * (2 / (1 - log (2 * U) / log x)) * (4 * log 2) * 1.04
        = (2 * U * (2 / (1 - log (2 * U) / log x))) * (4 * log 2 * 1.04) := by ring
      _ ≤ (2 * 2.9105e8 * 2.6354) * (4 * 0.6931471808 * 1.04) :=
          mul_le_mul a b (by nlinarith) (by norm_num)
      _ ≤ 4.489e9 := by norm_num
  have hs : sqrt (2 * U * (2 / (1 - log (2 * U) / log x)) * (4 * log 2) * 1.04) ≤ 67000 := by
    rw [sqrt_le_left (by norm_num)]; linarith
  linarith

/-- (8.16): with `|η̂₁(ξ)| ≤ ‖η₁‖₁ = 0.7` for `|ξ| ≤ 1/2` and `≤ 1/(π|ξ|)` beyond,
`∫_{|u| ≤ U} |η̂₁(u)| du ≤ 0.7 + (2/π) log (2U)`, and `10^{-6}` times that is at most
`1.4e-5`. -/
theorem eq816_le : 1e-6 * (0.7 + 2 / π * log (2 * U)) ≤ 1.4e-5 := by
  have hu := log_2U_le
  have hu0 := log_2U_pos
  have hp := pi_gt_d2
  have h : 2 / π ≤ 2 / 3.14 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  have : 2 / π * log (2 * U) ≤ 2 / 3.14 * 20.25 :=
    mul_le_mul h hu hu0.le (by norm_num)
  linarith

/-- F-0017 corrected: `∫ η₁(s) η₁(1 - s - t/K) ds = 2/3 + O*(Lip η₁ · ‖η₁‖₁ · t/K)` with
`Lip η₁ = 10`, `‖η₁‖₁ = 0.7`; averaged against `η₀`, supported in `[0, 1]` with
`‖η₀‖₁ = 1`, the error is at most `10 · 0.7 / K = 0.007`. -/
theorem conv_err : 10 * 0.7 / K = 0.007 := by unfold K; norm_num

/-- The tail `|α| > R` of the main integral, by `|η̂₁(ξ)| ≤ 1/(π|ξ|)`, Lemma 3.3, and
`|η̂₀| ≤ 1`: `x ∫_{|u| > U} du / (π² u²) = 2 / (π² U)` in units of `1/x`, at most `10^{-8}`. -/
theorem tail_le : 2 / (π ^ 2 * U) ≤ 1e-8 := by
  have hp := pi_gt_three
  have hU := U_ge
  rw [div_le_iff₀ (by positivity)]
  have : (9 : ℝ) ≤ π ^ 2 := by nlinarith
  nlinarith

/-- The paper's own bound for the `η₀` and `D` error, `10^{-3}`, survives F-0015: the
`η₀` error rises to at most `1.5e-6`, and `1.5e-6 · 2.6354 · 4 log 2 · 1.04` with the
`(1 + 10^{-10})³` from (8.13) is far below `10^{-3}`. -/
theorem eta0_err_le : 1.5e-6 * 2.6354 * (4 * log 2) * 1.04 * (1 + 1e-10) ^ 3 ≤ 1e-3 := by
  have := log_two_lt_d9
  nlinarith

/-- The budget: the five pieces sum to at most `0.076`. -/
theorem budget_sum : (1e-3 : ℝ) + 0.067 + 1.4e-5 + 0.007 + 1e-8 ≤ 0.076 := by norm_num

/-- Proposition 8.3's error, CONDITIONAL ON the analytic decomposition: if the error of (8.12)
in units of `x²(N₀/3)³/K` is at most the sum of the five pieces, each bounded as above, it is
at most `0.076`. -/
theorem prop83_error_of {E eD e15 e16 eC eT : ℝ}
    (hE : E ≤ eD + e15 + e16 + eC + eT) (hD : eD ≤ 1e-3) (h15 : e15 ≤ 0.067)
    (h16 : e16 ≤ 1.4e-5) (hC : eC ≤ 0.007) (hT : eT ≤ 1e-8) : E ≤ 0.076 := by
  linarith [budget_sum]

/-- The repair of F-0024 closes: with Proposition 8.3's error at most `0.076`, the corrected
Proposition 8.4 bound `8.001 - 0.94 · 2/3 · (1 - 10^{-10})²`, under `7.38`, times the `0.078`
of (8.18), is below `2/3 - 0.076`. -/
theorem f0024_repaired :
    0.078 * (8.001 - 0.94 * (2 / 3) * (1 - 1e-10) ^ 2) < (2 / 3 : ℝ) - 0.076 := by norm_num

#print axioms U_le
#print axioms U_ge
#print axioms log_x_ge
#print axioms log_2U_le
#print axioms cor47_factor_le
#print axioms eq815_le
#print axioms eq816_le
#print axioms conv_err
#print axioms tail_le
#print axioms eta0_err_le
#print axioms budget_sum
#print axioms prop83_error_of
#print axioms f0024_repaired

end LeanLab.Tao2012.Prop83
