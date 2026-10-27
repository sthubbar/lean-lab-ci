/-
P0014 H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Cor. 4.9, pages 47
and 48: `η* = η₂ *_M η` with `η₂ = η₁ *_M η₁`, `η₁ = 2 · 1_{[1/2,1]}`; the `x^{-1/2}` coefficients of
(4.56) are those of (4.52) times `∫ w^{-1/2} η₂(w) dw ≤ 1.37259`. Unit U-6063, CLOUD
20261020T0516Z-cloud35.

The slip of Prop. 4.8, `Sec48.coef_sqrtT0_gt`, carries over: 6.936 should be at least 6.9386, and
the Section 4.6 bound 377907/√q + 75.7 fails by about 36/√q, while Corollary 1.3's 380600/√q + 76
survives.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.HelfgottMajor.Sec48

namespace LeanLab.HelfgottMajor.Sec49
open Real LeanLab.HelfgottMajor.Sec48

/-- `∫ w^{-1/2} η₂(w) dw = (M η₁(1/2))² = (4(1 − 1/√2))²`, at most 1.37259, MATCH, 1.3725830. -/
theorem mellin_half_le : (4 * (1 - 1 / √2)) ^ 2 ≤ 1.37259 ∧ 1.37258 ≤ (4 * (1 - 1 / √2)) ^ 2 := by
  have h1 : (1.41421356 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √2 < 1.41421357 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3 : 1 / √2 < 1 / 1.41421356 := one_div_lt_one_div_of_lt (by norm_num) h1
  have h4 : 1 / 1.41421357 < 1 / √2 := one_div_lt_one_div_of_lt (by positivity) h2
  have h5 : 0 ≤ 4 * (1 - 1 / √2) := by norm_num at h3 ⊢; nlinarith
  constructor <;> nlinarith

/-- **(4.56), the printed chain**: `1.22 · 1.37259 ≤ 1.675`, `5.053 · 1.37259 ≤ 6.936`,
`1.423 · 1.37259 ≤ 1.954`, `37.19 · 1.37259 ≤ 51.047`. -/
theorem printed_chain : (1.22 : ℝ) * 1.37259 ≤ 1.675 ∧ (5.053 : ℝ) * 1.37259 ≤ 6.936 ∧
    (1.423 : ℝ) * 1.37259 ≤ 1.954 ∧ (37.19 : ℝ) * 1.37259 ≤ 51.047 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **With the true Prop. 4.8 coefficient the `√T₀` coefficient of (4.56) exceeds 6.938**, so 6.936
does not follow. -/
theorem cor49_coef_gt :
    6.938 < (17.21 * √mLog - log (2 * π * √(exp 1)) * √mTwo) * (4 * (1 - 1 / √2)) ^ 2 := by
  have h1 := coef_sqrtT0_gt
  have h2 := mellin_half_le.2
  nlinarith

/-- **Section 4.6: 377907 fails** with any coefficient above 6.938 ... -/
theorem printed_377907_fails {c : ℝ} (hc : 6.938 < c) :
    377907 < 1.675 * 10 ^ 4 * log (10 ^ 8 : ℝ) + c * 10 ^ 4 := by
  have := log_1e8.1; nlinarith

/-- ... and with the book's 5.056, times 1.37259, it stays at most 378000, below Corollary 1.3's
380600: Corollary 1.3 SURVIVES. -/
theorem cor13_survives : 1.675 * 10 ^ 4 * log (10 ^ 8 : ℝ) + 5.056 * 1.37259 * 10 ^ 4 ≤ 378000 := by
  have := log_1e8.2; nlinarith

end LeanLab.HelfgottMajor.Sec49
