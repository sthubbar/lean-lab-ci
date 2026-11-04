/-
P0059 arXiv 1407.7902v1 page 4, transfer from the integrated explicit formula.
An exact expression for J in terms of two polynomial-weighted psi-one integrals.
AI wrote this Lean code. CODEX task301. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.PsiParts301

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory
open Task64
open LeanLab.Dudek2014.Section22 (psi1)

/-- The actual smoothed psi average transfers exactly to psi-one integrals. -/
theorem psiAverage_eq_psi1_integrals {m : ℕ} (hm : 0 < m) {δ X : ℝ}
    (hδ : 0 < δ) (hX : 0 < X) (u : ℝ) :
    psiAverage m δ u X =
      ((∫ t in (0 : ℝ)..1, psi1 (X * (1 + δ * t)) * weightD m t) -
        Real.exp (-u) * (∫ t in (0 : ℝ)..1,
          psi1 (Real.exp u * (X * (1 + δ * t))) * weightD m t)) /
        (X * δ * (∫ t in (0 : ℝ)..1, weight m t)) := by
  have hL := integral_psi_affine_weight hm hX (mul_pos hX hδ)
  have hU := integral_psi_affine_weight hm (mul_pos (Real.exp_pos u) hX)
    (mul_pos (mul_pos (Real.exp_pos u) hX) hδ)
  have hLarg : ∀ t : ℝ, X + X * δ * t = X * (1 + δ * t) := by intro t; ring
  have hUarg : ∀ t : ℝ, Real.exp u * X + (Real.exp u * X * δ) * t =
      Real.exp u * (X * (1 + δ * t)) := by intro t; ring
  simp_rw [hLarg] at hL
  simp_rw [hUarg] at hU
  have hmono : Monotone (fun t : ℝ => X * (1 + δ * t)) := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hst hδ.le)) hX.le
  have hUmono : Monotone (fun t : ℝ => Real.exp u * (X * (1 + δ * t))) := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left (hmono hst) (Real.exp_nonneg u)
  have hLi := ((Chebyshev.psi_mono.comp hmono).intervalIntegrable (μ := volume) (a := 0) (b := 1)).mul_continuousOn
    (weight_continuous m).continuousOn
  have hUi := ((Chebyshev.psi_mono.comp hUmono).intervalIntegrable (μ := volume) (a := 0) (b := 1)).mul_continuousOn
    (weight_continuous m).continuousOn
  simp only [Function.comp_def] at hLi hUi
  have hsplit : (fun t : ℝ =>
      (Chebyshev.psi (Real.exp u * (X * (1 + δ * t))) - Chebyshev.psi (X * (1 + δ * t))) * weight m t) =
      (fun t => Chebyshev.psi (Real.exp u * (X * (1 + δ * t))) * weight m t -
        Chebyshev.psi (X * (1 + δ * t)) * weight m t) := by
    funext t
    ring
  unfold psiAverage
  rw [hsplit, intervalIntegral.integral_sub hUi hLi, Real.exp_neg]
  have hmass := (weight_mass_pos m).ne'
  field_simp
  simp_rw [mul_assoc] at hL hU ⊢
  linear_combination hU - Real.exp u * hL

end LeanLab.KadiriLumley2014.Task301
