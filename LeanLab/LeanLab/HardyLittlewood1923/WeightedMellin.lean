import LeanLab.HardyLittlewood1923.ComplexGammaIdentity
import LeanLab.HardyLittlewood1923.WeightedContour

/-!
AI wrote this Lean code for CODEX task52.
The weighted Dirichlet Mellin identity is P0004 page 8 equation 2.13.
-/

open Complex Real Set Filter MeasureTheory
open LeanLab.PNTPort.PsiChi (a_zero LSeries_eq_tsum summable_norm_div LSeries_chi_vonMangoldt_eq)

namespace LeanLab.HardyLittlewood1923.Task52

lemma positive_scale_cpow {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (s : ℂ) :
    ((r : ℂ) * z) ^ s = (r : ℂ) ^ s * z ^ s := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 hz),
    Complex.cpow_def_of_ne_zero hr0, Complex.cpow_def_of_ne_zero hz,
    Complex.log_ofReal_mul hr hz, Complex.ofReal_log hr.le, add_mul, Complex.exp_add]

/-- Mellin inversion and absolute Fubini for von Mangoldt bounded coefficients. -/
theorem dirichlet_exponential_mellin {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 3 / 2) {z : ℂ} (hz : 0 < z.re) :
    (1 / (2 * (π : ℂ))) *
      (∫ t : ℝ, LSeries a ((σ : ℂ) + t * I) *
        (Complex.Gamma ((σ : ℂ) + t * I) * z ^ (-((σ : ℂ) + t * I)))) =
      ∑' n : ℕ, a n * Complex.exp (-(n : ℂ) * z) := by
  let H : ℝ → ℂ := fun t => Complex.Gamma ((σ : ℂ) + t * I) *
    z ^ (-((σ : ℂ) + t * I))
  let F : ℕ → ℝ → ℂ := fun n t => a n / (n : ℂ) ^ ((σ : ℂ) + t * I) * H t
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have ha0 := a_zero ha
  have hH : Integrable H := gamma_kernel_integrable (by linarith) hσ2 hz
  have hn : ∀ n t, ‖F n t‖ = (‖a n‖ / (n : ℝ) ^ σ) * ‖H t‖ := by
    intro n t
    by_cases hn0 : n = 0
    · simp [F, hn0, ha0]
    · dsimp [F]
      rw [norm_mul, norm_div, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn0)]
      simp
  have hF : ∀ n : ℕ, Integrable (F n) := by
    intro n
    by_cases hn0 : n = 0
    · simpa [F, hn0, ha0] using (integrable_zero : Integrable (fun _ : ℝ => (0 : ℂ)))
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hc : Continuous (fun t : ℝ => a n / (n : ℂ) ^ ((σ : ℂ) + t * I)) := by
      apply Continuous.div₀ continuous_const
        (Continuous.const_cpow (by fun_prop) (Or.inl hnc))
      intro t
      simp [Complex.cpow_eq_zero_iff, hnc]
    exact Integrable.mono' (hH.norm.const_mul (‖a n‖ / (n : ℝ) ^ σ))
      (hc.aestronglyMeasurable.mul hH.aestronglyMeasurable)
      (Eventually.of_forall fun t => (hn n t).le)
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    have he : (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) =
        (fun n : ℕ => (‖a n‖ / (n : ℝ) ^ σ) * ∫ t : ℝ, ‖H t‖) := by
      funext n
      simp_rw [hn]
      rw [integral_const_mul]
    rw [he]
    exact (summable_norm_div ha hσ).mul_right _
  have hex := integral_tsum_of_summable_integral_norm hF hsum
  have hline : (fun t : ℝ => LSeries a ((σ : ℂ) + t * I) * H t) =
      (fun t : ℝ => ∑' n : ℕ, F n t) := by
    funext t
    rw [LSeries_eq_tsum ha0, ← tsum_mul_right]
  have hi : ∀ n : ℕ, (1 / (2 * (π : ℂ))) * (∫ t : ℝ, F n t) =
      a n * Complex.exp (-(n : ℂ) * z) := by
    intro n
    by_cases hn0 : n = 0
    · simp [F, hn0, ha0]
    have hnp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hp : 0 < ((n : ℂ) * z).re := by simpa using mul_pos hnp hz
    have he : ∀ t : ℝ, F n t = a n *
        (Complex.Gamma ((σ : ℂ) + t * I) * ((n : ℂ) * z) ^ (-((σ : ℂ) + t * I))) := by
      intro t
      dsimp [F, H]
      have hscale := positive_scale_cpow hnp hz0 (-((σ : ℂ) + t * I))
      norm_cast at hscale
      rw [hscale]
      simp only [Complex.cpow_neg, div_eq_mul_inv]
      ring
    simp_rw [he]
    rw [integral_const_mul]
    calc _ = a n * ((1 / (2 * (π : ℂ))) *
          ∫ t : ℝ, Complex.Gamma ((σ : ℂ) + t * I) *
            ((n : ℂ) * z) ^ (-((σ : ℂ) + t * I))) := by ring
      _ = a n * Complex.exp (-((n : ℂ) * z)) := by
        rw [gamma_inverse_complex (by linarith) hσ2 hp]
      _ = _ := by rw [neg_mul]
  change (1 / (2 * (π : ℂ))) * (∫ t : ℝ, LSeries a ((σ : ℂ) + t * I) * H t) = _
  rw [hline, ← hex, ← tsum_mul_left]
  exact tsum_congr hi

/-- The exponential weighted character sum is its right line Mellin integral. -/
theorem weightedSum_mellin_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 3 / 2) {z : ℂ} (hz : 0 < z.re) :
    weightedSum χ z = (1 / (2 * (π : ℂ))) *
      (∫ t : ℝ, weightedKernel χ z ((σ : ℂ) + t * I)) := by
  have ha : ∀ n : ℕ,
      ‖χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
        ArithmeticFunction.vonMangoldt n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
  have h := dirichlet_exponential_mellin ha hσ hσ2 hz
  rw [weightedSum]
  rw [← h]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  have hL := LSeries_chi_vonMangoldt_eq χ (s := (σ : ℂ) + t * I)
    (by simpa using hσ)
  change LSeries ((fun n : ℕ => χ (n : ZMod q)) *
    (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))) _ * _ = _
  rw [hL]
  simp [weightedKernel, neg_div, mul_assoc]

#print axioms positive_scale_cpow
#print axioms dirichlet_exponential_mellin
#print axioms weightedSum_mellin_right

end LeanLab.HardyLittlewood1923.Task52
