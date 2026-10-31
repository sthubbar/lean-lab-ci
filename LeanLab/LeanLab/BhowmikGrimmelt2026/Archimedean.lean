/-
The inner beta integral from equation 7.21, page 29.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

/-- The inner integral J_v in equation 7.21, with N explicit. -/
noncomputable def Jphi (ϕ : ℝ → ℝ) (N v : ℝ) (ρ₁ ρ₂ : ℂ) : ℂ :=
  ∫ σ in (0 : ℝ)..1,
    ((ϕ (v * σ / N) * ϕ (v * (1 - σ) / N) : ℝ) : ℂ) *
      (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)

/-- At v equal to N, the inner integral is the paper's weighted beta factor. -/
theorem Jphi_at_N (ϕ : ℝ → ℝ) {N : ℝ} (hN : N ≠ 0) (ρ₁ ρ₂ : ℂ) :
    Jphi ϕ N N ρ₁ ρ₂ = Bphi ϕ ρ₁ ρ₂ := by
  unfold Jphi Bphi
  apply intervalIntegral.integral_congr
  intro σ hσ
  dsimp only
  rw [mul_div_cancel_left₀ σ hN, mul_div_cancel_left₀ (1 - σ) hN]

/-- At the two real unit arguments, normalization gives one for every nonzero N. -/
theorem Jphi_at_N_one_one {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N : ℝ} (hN : N ≠ 0) :
    Jphi ϕ N N 1 1 = 1 := by
  rw [Jphi_at_N ϕ hN, Bphi_one_one hϕ]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.Jphi_at_N
#print axioms LeanLab.BhowmikGrimmelt2026.Jphi_at_N_one_one
