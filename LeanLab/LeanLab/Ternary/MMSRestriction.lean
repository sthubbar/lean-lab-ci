/-
P0028, arXiv 1610.02017, Lemma 4.3 item 4 and equation 4.1, pages 9 and 10.
The elementary restriction norm contraction once a Fourier multiplier is known.
The multiplier identity is an explicit hypothesis. It is not supplied for truncated smoothing.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSTransference

namespace LeanLab.Ternary.MMS

/-- The finite interval Fourier transform is continuous. -/
theorem continuous_fhat (N : ℕ) (f : ℕ → ℝ) : Continuous (fhat N f) := by
  unfold fhat
  fun_prop

/-- Pointwise Fourier norm domination implies domination of the restriction norm. -/
theorem fhatLq_mono (N : ℕ) (f g : ℕ → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hfg : ∀ γ : ℝ, ‖fhat N g γ‖ ≤ ‖fhat N f γ‖) :
    fhatLq N g q ≤ fhatLq N f q := by
  have hc (u : ℕ → ℝ) : Continuous (fun γ : ℝ => ‖fhat N u γ‖ ^ q) :=
    (continuous_fhat N u).norm.rpow_const (fun _ => Or.inr hq)
  unfold fhatLq
  apply Real.rpow_le_rpow
  · exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun γ => Real.rpow_nonneg (norm_nonneg _) _)
  · exact intervalIntegral.integral_mono (by norm_num)
      ((hc g).intervalIntegrable 0 1) ((hc f).intervalIntegrable 0 1)
      (fun γ => Real.rpow_le_rpow (norm_nonneg _) (hfg γ) hq)
  · positivity

/-- A real multiplier in the unit interval contracts the restriction norm. -/
theorem fhatLq_le_of_real_multiplier (N : ℕ) (f g : ℕ → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (m : ℝ → ℝ) (hm : ∀ γ, 0 ≤ m γ ∧ m γ ≤ 1)
    (hhat : ∀ γ, fhat N g γ = fhat N f γ * (m γ : ℂ)) :
    fhatLq N g q ≤ fhatLq N f q := by
  apply fhatLq_mono N f g hq
  intro γ
  rw [hhat γ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm γ).1]
  exact mul_le_of_le_one_right (norm_nonneg _) (hm γ).2

end LeanLab.Ternary.MMS
