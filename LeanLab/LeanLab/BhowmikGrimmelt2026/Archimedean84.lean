/-
Support and phase steps in the proof of Lemma 7.6, page 29 display 7.21.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Archimedean

namespace LeanLab.BhowmikGrimmelt2026

/-- Page 29 display 7.21. A nonzero pair cutoff forces v to be comparable to positive N. -/
theorem phi_pair_support84 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N v σ : ℝ} (hN : 0 < N)
    (hne : ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) ≠ 0) :
    (2 / 5) * N < v ∧ v < (8 / 5) * N := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
  have hs1 := hϕ.supp (subset_tsupport ϕ h1)
  have hs2 := hϕ.supp (subset_tsupport ϕ h2)
  have hl1 := (lt_div_iff₀ hN).mp hs1.1
  have hu1 := (div_lt_iff₀ hN).mp hs1.2
  have hl2 := (lt_div_iff₀ hN).mp hs2.1
  have hu2 := (div_lt_iff₀ hN).mp hs2.2
  constructor <;> nlinarith only [hl1, hl2, hu1, hu2]

/-- Page 29 display 7.21. The nonzero cutoff is supported away from both sigma endpoints. -/
theorem phi_pair_sigma_support84 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N v σ : ℝ} (hN : 0 < N)
    (hne : ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) ≠ 0) :
    (1 / 5 : ℝ) < σ ∧ σ < 4 / 5 := by
  have hv : 0 < v := by
    have hs := phi_pair_support84 hϕ hN hne
    nlinarith [hs.1]
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
  have hs1 := hϕ.supp (subset_tsupport ϕ h1)
  have hs2 := hϕ.supp (subset_tsupport ϕ h2)
  have hl1 := (lt_div_iff₀ hN).mp hs1.1
  have hu1 := (div_lt_iff₀ hN).mp hs1.2
  have hl2 := (lt_div_iff₀ hN).mp hs2.1
  have hu2 := (div_lt_iff₀ hN).mp hs2.2
  constructor
  · apply (mul_lt_mul_iff_right₀ hv).mp
    nlinarith only [hl1, hu2]
  · apply (mul_lt_mul_iff_right₀ hv).mp
    nlinarith only [hu1, hl2]

/-- Page 29 display 7.21. J_v vanishes outside the effective v interval. -/
theorem Jphi_eq_zero_outside84 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N v : ℝ} (hN : 0 < N)
    (hout : v ≤ (2 / 5) * N ∨ (8 / 5) * N ≤ v) (ρ₁ ρ₂ : ℂ) :
    Jphi ϕ N v ρ₁ ρ₂ = 0 := by
  have hzero (σ : ℝ) : ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) = 0 := by
    by_contra hn
    have hv := phi_pair_support84 hϕ hN hn
    rcases hout with hl | hu
    · linarith [hv.1]
    · linarith [hv.2]
  unfold Jphi
  simp only [hzero, Complex.ofReal_zero, zero_mul, intervalIntegral.integral_zero]

/-- Page 29, proof of 7.19. The derivative of the sigma phase. -/
theorem sigma_phase_derivative84 (t₁ t₂ : ℝ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    HasDerivAt (fun x : ℝ => t₁ * Real.log x + t₂ * Real.log (1 - x))
      (t₁ / σ - t₂ / (1 - σ)) σ := by
  have h1 := (Real.hasDerivAt_log (ne_of_gt hσ0)).const_mul t₁
  have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) σ := by
    exact (hasDerivAt_id σ).const_sub 1
  have h2 := (hinner.log (by linarith : 1 - σ ≠ 0)).const_mul t₂
  convert h1.add h2 using 1 <;> simp [div_eq_mul_inv] <;> ring

/-- Page 29, proof of 7.19. Opposite signs prevent a stationary sigma phase. -/
theorem sigma_phase_lower84 {t₁ t₂ σ : ℝ} (hprod : t₁ * t₂ < 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    |t₁| + |t₂| ≤ |t₁ / σ - t₂ / (1 - σ)| := by
  rcases mul_neg_iff.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hl : t₁ ≤ t₁ / σ := (le_div_iff₀ hσ0).mpr (by
      nlinarith only [mul_nonneg h1.le (sub_nonneg.mpr hσ1.le)])
    have hr : -t₂ ≤ -t₂ / (1 - σ) := (le_div_iff₀ (sub_pos.mpr hσ1)).mpr (by
      nlinarith only [mul_nonneg (neg_nonneg.mpr h2.le) hσ0.le])
    rw [neg_div] at hr
    rw [abs_of_pos h1, abs_of_neg h2]
    linarith only [hl, hr, le_abs_self (t₁ / σ - t₂ / (1 - σ))]
  · have hl : -t₁ ≤ -t₁ / σ := (le_div_iff₀ hσ0).mpr (by
      nlinarith only [mul_nonneg (neg_nonneg.mpr h1.le) (sub_nonneg.mpr hσ1.le)])
    have hr : t₂ ≤ t₂ / (1 - σ) := (le_div_iff₀ (sub_pos.mpr hσ1)).mpr (by
      nlinarith only [mul_nonneg h2.le hσ0.le])
    rw [neg_div] at hl
    rw [abs_of_neg h1, abs_of_pos h2]
    linarith only [hl, hr, neg_le_abs (t₁ / σ - t₂ / (1 - σ))]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.phi_pair_support84

#print axioms LeanLab.BhowmikGrimmelt2026.phi_pair_sigma_support84

#print axioms LeanLab.BhowmikGrimmelt2026.Jphi_eq_zero_outside84

#print axioms LeanLab.BhowmikGrimmelt2026.sigma_phase_derivative84

#print axioms LeanLab.BhowmikGrimmelt2026.sigma_phase_lower84
