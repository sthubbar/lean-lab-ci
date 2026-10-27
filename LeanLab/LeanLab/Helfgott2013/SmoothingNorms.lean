/-
Actual smoothing norm inputs for Helfgott, arXiv:1312.7748v2, Section 7.2, pages 60 to 61.
AI wrote this Lean code, OpenAI Codex, task31, 2026-10-22.
Binary Goldbach remains open.
-/
import LeanLab.Helfgott2013.MellinL1

open Real MeasureTheory Set

namespace LeanLab.Helfgott2013.SmoothingNorms
open GaussianL2 MellinL2 MellinL1 MellinSup

/-- The proved analytic smoothing inputs for every positive scale, including k = 49. -/
theorem etaStar_bounds (k : ℝ) (hk : 0 < k) :
    IntegrableOn (etaStar k) (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun w : ℝ => etaStar k w ^ 2) (Ioi 0) ∧
      (∫ w in Ioi (0 : ℝ), |etaStar k w|) = Real.sqrt (Real.pi / 2) / k ∧
      (∫ w in Ioi (0 : ℝ), etaStar k w ^ 2) ≤ 1.77082 / k ∧
      ∀ w : ℝ, 0 ≤ w → 0 ≤ etaStar k w ∧ |etaStar k w| ≤ 1.414 ∧
        |etaStar k w * Real.posLog (k * w)| ≤ 0.732513 ∧
        |etaStar k w * w| ≤ 1.15942 / k := by
  have h1 := etaStar_abs_integral k hk
  have h2 := etaStar_sq_integral k hk
  refine ⟨h1.1, h2.1, h1.2, h2.2, ?_⟩
  intro w hw
  refine ⟨(mellin_sup (k * w)).1, (mellin_sup (k * w)).2,
    mellin_posLog_sup (mul_nonneg hk.le hw), ?_⟩
  have he : etaStar k w * w = (mellin (k * w) * (k * w)) / k := by
    unfold etaStar
    field_simp
  rw [he, abs_div, abs_of_pos hk]
  exact (div_le_div_iff_of_pos_right hk).mpr
    ((mellin_mul_sup (mul_nonneg hk.le hw)).trans LeanLab.Helfgott2013.phi_t_value)

#print axioms etaStar_bounds

end LeanLab.Helfgott2013.SmoothingNorms
