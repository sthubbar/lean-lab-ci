/-
Combining the two Taylor estimates on page 29 in the proof of display 7.20.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Power107

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF. Page 29 proof of 7.20. The normalized power times J_v has uniform first order error. -/
theorem weighted_beta_taylor107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 0 < N → ∀ v : ℝ,
      v / N ∈ Set.Icc (2 / 5 : ℝ) (8 / 5) → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 →
      ‖((v / N : ℝ) : ℂ) ^ (ρ₁ + ρ₂ - 1) * Jphi ϕ N v ρ₁ ρ₂ - Bphi ϕ ρ₁ ρ₂‖ ≤
        C * (1 + |(ρ₁ + ρ₂).im|) * |v / N - 1| := by
  obtain ⟨CJ, hCJ, hJ⟩ := Jphi_uniform107 hϕ
  obtain ⟨CT, hCT, hT⟩ := Jphi_taylor107 hϕ
  refine ⟨(25 / 4) * CJ + CT, by positivity, ?_⟩
  intro N hN v hv ρ₁ ρ₂ h₁ h₁' h₂ h₂'
  have hzre : -1 ≤ (ρ₁ + ρ₂ - 1).re ∧ (ρ₁ + ρ₂ - 1).re ≤ 1 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
    constructor <;> linarith
  have hp : ‖((v / N : ℝ) : ℂ) ^ (ρ₁ + ρ₂ - 1) - 1‖ ≤
      (25 / 4 : ℝ) * (1 + |(ρ₁ + ρ₂).im|) * |v / N - 1| :=
    (cpow_near_one107 hv hzre).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sum_exponent_norm107 h₁ h₁' h₂ h₂') (by norm_num))
        (abs_nonneg _))
  rw [show ((v / N : ℝ) : ℂ) ^ (ρ₁ + ρ₂ - 1) * Jphi ϕ N v ρ₁ ρ₂ - Bphi ϕ ρ₁ ρ₂ =
    (((v / N : ℝ) : ℂ) ^ (ρ₁ + ρ₂ - 1) - 1) * Jphi ϕ N v ρ₁ ρ₂ +
      (Jphi ϕ N v ρ₁ ρ₂ - Bphi ϕ ρ₁ ρ₂) by ring]
  calc
    _ ≤ ‖(((v / N : ℝ) : ℂ) ^ (ρ₁ + ρ₂ - 1) - 1) * Jphi ϕ N v ρ₁ ρ₂‖ +
        ‖Jphi ϕ N v ρ₁ ρ₂ - Bphi ϕ ρ₁ ρ₂‖ := norm_add_le _ _
    _ ≤ ((25 / 4 : ℝ) * (1 + |(ρ₁ + ρ₂).im|) * |v / N - 1|) * CJ + CT * |v / N - 1| := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul hp (hJ N hN v ρ₁ ρ₂ h₁ h₂) (norm_nonneg _) (by positivity))
        (hT N hN v ρ₁ ρ₂ h₁ h₂)
    _ ≤ _ := by
      have hf : 1 ≤ 1 + |(ρ₁ + ρ₂).im| := by linarith [abs_nonneg (ρ₁ + ρ₂).im]
      have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hCT) (abs_nonneg (v / N - 1))
      nlinarith only [hm]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.weighted_beta_taylor107
