/-
Absolute bounds for the inner integral on page 29 display 7.21.
These bounds do not supply the oscillatory decay in display 7.19.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Archimedean84

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF. Page 29, the sigma support in the proof of 7.19 bounds each power by five. -/
theorem cutoff_cpow_norm107 {σ : ℝ} (hσ : (1 / 5 : ℝ) < σ ∧ σ < 4 / 5)
    {ρ : ℂ} (hρ : 0 < ρ.re) : ‖(σ : ℂ) ^ (ρ - 1)‖ ≤ 5 := by
  have hσ0 : 0 < σ := by linarith [hσ.1]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hσ0, Complex.sub_re, Complex.one_re]
  calc
    σ ^ (ρ.re - 1) ≤ σ ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hσ0 (by linarith [hσ.2]) (by linarith)
    _ = σ⁻¹ := Real.rpow_neg_one σ
    _ ≤ 5 := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hσ0).mpr (by linarith [hσ.1])

/-- LEAF. Page 29 display 7.21. Absolute integration gives a bound with no frequency decay. -/
theorem Jphi_absolute107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x : ℝ, |ϕ x| ≤ M) {N : ℝ} (hN : 0 < N) (v : ℝ)
    (ρ₁ ρ₂ : ℂ) (hρ₁ : 0 < ρ₁.re) (hρ₂ : 0 < ρ₂.re) :
    ‖Jphi ϕ N v ρ₁ ρ₂‖ ≤ 25 * M ^ 2 := by
  unfold Jphi
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := 25 * M ^ 2) (f := fun σ : ℝ =>
      ((ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) : ℝ) : ℂ) *
      (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)) (by
        intro σ hσ
        by_cases hz : ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) = 0
        · simp only [hz, Complex.ofReal_zero, zero_mul, norm_zero]
          positivity
        · have hs := phi_pair_sigma_support84 hϕ hN hz
          have hs' : (1 / 5 : ℝ) < 1 - σ ∧ 1 - σ < 4 / 5 := by constructor <;> linarith [hs.1, hs.2]
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
          calc
            _ ≤ M * M * 5 * 5 := by
              gcongr
              · exact hbound _
              · exact hbound _
              · exact cutoff_cpow_norm107 hs hρ₁
              · exact cutoff_cpow_norm107 hs' hρ₂
            _ = 25 * M ^ 2 := by ring)
  simpa only [sub_zero, abs_one, mul_one] using hb

/-- Page 29 display 7.21. The inner integral is uniformly bounded over positive scales
and complex arguments with positive real parts. This gives no arbitrary power decay. -/
theorem Jphi_uniform107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 0 < N → ∀ v : ℝ, ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → 0 < ρ₂.re → ‖Jphi ϕ N v ρ₁ ρ₂‖ ≤ C := by
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  refine ⟨25 * (max M 0) ^ 2, by positivity, ?_⟩
  intro N hN v ρ₁ ρ₂ hρ₁ hρ₂
  apply Jphi_absolute107 hϕ (le_max_right M 0) _ hN v ρ₁ ρ₂ hρ₁ hρ₂
  intro x
  exact le_trans (by simpa only [Real.norm_eq_abs] using hM x) (le_max_left _ _)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.cutoff_cpow_norm107
#print axioms LeanLab.BhowmikGrimmelt2026.Jphi_absolute107
#print axioms LeanLab.BhowmikGrimmelt2026.Jphi_uniform107
