/-
The cutoff variation in the proof of display 7.20 on page 29.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Absolute107
import LeanLab.BhowmikGrimmelt2026.Integration107

namespace LeanLab.BhowmikGrimmelt2026

open scoped NNReal

/-- LEAF. Page 29 display 7.21. The cutoff makes the full sigma integrand continuous. -/
theorem continuous_Jphi_integrand107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N : ℝ} (hN : 0 < N)
    (v : ℝ) (ρ₁ ρ₂ : ℂ) : Continuous (fun σ : ℝ =>
      ((ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) : ℝ) : ℂ) *
        (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)) := by
  by_cases hv : 0 < v
  · have hc (ρ : ℂ) : Continuous (fun σ : ℝ => (ϕ (v * σ / N) : ℂ) * (σ : ℂ) ^ (ρ - 1)) := by
      convert continuous_cutoff_cpow107 hϕ (div_pos hN hv) ρ using 1
      ext σ
      congr 2
      field_simp
      <;> ring
    have hs : Continuous (fun σ : ℝ => (ϕ (v * (1 - σ) / N) : ℂ) *
        ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)) :=
      (hc ρ₂).comp (show Continuous (fun σ : ℝ => 1 - σ) by fun_prop)
    convert (hc ρ₁).mul hs using 1
    ext σ
    simp only [Pi.mul_apply]
    push_cast
    ring
  · have hz (σ : ℝ) : ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) = 0 := by
      by_contra hn
      have hs := (phi_pair_support84 hϕ hN hn).1
      have : 0 < v := by nlinarith
      exact hv this
    simpa only [hz, Complex.ofReal_zero, zero_mul] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))

/-- LEAF. Page 29 proof of 7.20. A bounded Lipschitz cutoff varies at first order in v / N. -/
theorem cutoff_pair_lipschitz107 {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x : ℝ, |ϕ x| ≤ M) {L : ℝ≥0} (hL : LipschitzWith L ϕ)
    (N v : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    |ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) - ϕ σ * ϕ (1 - σ)| ≤
      2 * M * L * |v / N - 1| := by
  have hb (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      |ϕ (v * s / N) - ϕ s| ≤ L * |v / N - 1| := by
    have hl := hL.norm_sub_le (v * s / N) s
    simp only [Real.norm_eq_abs] at hl
    rw [show v * s / N - s = (v / N - 1) * s by ring, abs_mul, abs_of_nonneg hs.1] at hl
    have hm := mul_le_mul_of_nonneg_left hs.2
      (mul_nonneg L.coe_nonneg (abs_nonneg (v / N - 1)))
    exact hl.trans (by nlinarith only [hm])
  have hb₁ := hb σ hσ
  have hb₂ := hb (1 - σ) (by constructor <;> linarith [hσ.1, hσ.2])
  calc
    _ = |(ϕ (v * σ / N) - ϕ σ) * ϕ (v * (1 - σ) / N) +
        ϕ σ * (ϕ (v * (1 - σ) / N) - ϕ (1 - σ))| := by congr 1; ring
    _ ≤ |ϕ (v * σ / N) - ϕ σ| * |ϕ (v * (1 - σ) / N)| +
        |ϕ σ| * |ϕ (v * (1 - σ) / N) - ϕ (1 - σ)| := by
      simpa only [abs_mul] using abs_add_le
        ((ϕ (v * σ / N) - ϕ σ) * ϕ (v * (1 - σ) / N))
        (ϕ σ * (ϕ (v * (1 - σ) / N) - ϕ (1 - σ)))
    _ ≤ (L * |v / N - 1|) * M + M * (L * |v / N - 1|) := by
      exact add_le_add
        (mul_le_mul hb₁ (hbound _) (abs_nonneg _) (by positivity))
        (mul_le_mul (hbound _) hb₂ (abs_nonneg _) hM)
    _ = _ := by ring

/-- LEAF. Page 29 proof of 7.20. Uniform Taylor error for the inner beta factor. -/
theorem Jphi_taylor107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 0 < N → ∀ v : ℝ, ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → 0 < ρ₂.re →
      ‖Jphi ϕ N v ρ₁ ρ₂ - Bphi ϕ ρ₁ ρ₂‖ ≤ C * |v / N - 1| := by
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  let M' := max M 0
  have hM' : 0 ≤ M' := le_max_right _ _
  have hbound : ∀ x : ℝ, |ϕ x| ≤ M' := fun x =>
    le_trans (by simpa only [Real.norm_eq_abs] using hM x) (le_max_left _ _)
  refine ⟨50 * M' * L, by positivity, ?_⟩
  intro N hN v ρ₁ ρ₂ hρ₁ hρ₂
  rw [← Jphi_at_N ϕ hN.ne' ρ₁ ρ₂]
  unfold Jphi
  rw [← intervalIntegral.integral_sub
    ((continuous_Jphi_integrand107 hϕ hN v ρ₁ ρ₂).intervalIntegrable 0 1)
    ((continuous_Jphi_integrand107 hϕ hN N ρ₁ ρ₂).intervalIntegrable 0 1)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := 50 * M' * L * |v / N - 1|) (f := fun σ : ℝ =>
      (((ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) : ℝ) : ℂ) *
        (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)) -
      (((ϕ (N * σ / N) * ϕ (N * (1 - σ) / N) : ℝ) : ℂ) *
        (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1))) (by
      intro σ hσ
      rw [mul_div_cancel_left₀ σ hN.ne', mul_div_cancel_left₀ (1 - σ) hN.ne',
        ← sub_mul, ← sub_mul, ← Complex.ofReal_sub]
      by_cases hz : ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) - ϕ σ * ϕ (1 - σ) = 0
      · simp only [hz, Complex.ofReal_zero, zero_mul, norm_zero]
        positivity
      · have hs : (1 / 5 : ℝ) < σ ∧ σ < 4 / 5 := by
          by_cases hzv : ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) = 0
          · have hzb : ϕ σ * ϕ (1 - σ) ≠ 0 := by
              intro hh
              exact hz (by rw [hzv, hh, sub_self])
            exact hϕ.supp (subset_tsupport ϕ (mul_ne_zero_iff.mp hzb).1)
          · exact phi_pair_sigma_support84 hϕ hN hzv
        have hs' : (1 / 5 : ℝ) < 1 - σ ∧ 1 - σ < 4 / 5 := by constructor <;> linarith [hs.1, hs.2]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          _ ≤ (2 * M' * L * |v / N - 1|) * 5 * 5 := by
            gcongr
            · exact cutoff_pair_lipschitz107 hM' hbound hL N v (by constructor <;> linarith [hs.1, hs.2])
            · exact cutoff_cpow_norm107 hs hρ₁
            · exact cutoff_cpow_norm107 hs' hρ₂
          _ = _ := by ring)
  simpa only [sub_zero, abs_one, mul_one] using hb

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.continuous_Jphi_integrand107
#print axioms LeanLab.BhowmikGrimmelt2026.cutoff_pair_lipschitz107

#print axioms LeanLab.BhowmikGrimmelt2026.Jphi_taylor107
