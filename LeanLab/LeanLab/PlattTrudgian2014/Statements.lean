/-
Platt, Trudgian 2014, Linnik's approximation to Goldbach's conjecture, and other problems,
P0024, arXiv 1404.5669v2. The paper has no labelled theorems. Its new results are numerical:
lambda ≤ 0.8594000 unconditionally and ≤ 0.7163436 on GRH, C₃ ≥ 3.02858417 for K = 11 and
C₃ ≥ 3.011112 for K = 6, which give "K ≥ 11.0953" and "K ≥ 6.09353", so no new K.
Here: the admissibility inequality (2), lambda^(K-2) < C₃ / ((C₁ - 2) C₂ + c C₀⁻¹ log 2),
with the paper's constants, and a kernel check that their numbers give K = 12 but not 11,
and on GRH K = 7 but not 6. The analytic meaning of lambda is not formalized.
Constants: C₀ > 0.6601618158 lower bound, C₂ < 1.93656 upper bound, C₁ = 7.8209 Liu-Lü,
c = 109/154 unconditional, 1/2 on GRH.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.PlattTrudgian2014

/-- The right side of inequality (2). -/
noncomputable def rhs (C₀ C₁ C₂ C₃ c : ℝ) : ℝ := C₃ / ((C₁ - 2) * C₂ + c / C₀ * Real.log 2)

/-- Inequality (2): `K` is admissible for these constants. -/
def Admissible (lam C₀ C₁ C₂ C₃ c : ℝ) (K : ℕ) : Prop := lam ^ (K - 2) < rhs C₀ C₁ C₂ C₃ c

theorem log2_bounds : 0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

/-- The denominator with the paper's unconditional constants lies in a narrow range. -/
theorem rhs_bounds_uncond :
    0.2520 < rhs 0.6601618158 7.8209 1.93656 3.02858417 (109 / 154) ∧
      rhs 0.6601618158 7.8209 1.93656 3.02858417 (109 / 154) < 0.2521 := by
  obtain ⟨h1, h2⟩ := log2_bounds
  unfold rhs
  have hd : 0 < (7.8209 - 2) * 1.93656 + 109 / 154 / 0.6601618158 * Real.log 2 := by positivity
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ hd]; nlinarith

/-- Unconditionally, lambda = 0.8594 admits K = 12. -/
theorem admissible_12 : Admissible 0.8594 0.6601618158 7.8209 1.93656 3.02858417 (109 / 154) 12 := by
  unfold Admissible
  have := rhs_bounds_uncond.1
  norm_num at this ⊢
  linarith

/-- But not K = 11: the paper's "just short of being able to take K = 11". -/
theorem not_admissible_11 :
    ¬ Admissible 0.8594 0.6601618158 7.8209 1.93656 3.02858417 (109 / 154) 11 := by
  unfold Admissible
  have := rhs_bounds_uncond.2
  norm_num at this ⊢
  linarith

theorem rhs_bounds_GRH :
    0.2552 < rhs 0.6601618158 7.8209 1.93656 3.011112 (1 / 2) ∧
      rhs 0.6601618158 7.8209 1.93656 3.011112 (1 / 2) < 0.2553 := by
  obtain ⟨h1, h2⟩ := log2_bounds
  unfold rhs
  have hd : 0 < (7.8209 - 2) * 1.93656 + 1 / 2 / 0.6601618158 * Real.log 2 := by positivity
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ hd]; nlinarith

/-- On GRH, lambda = 0.7163436 admits K = 7. -/
theorem admissible_7_GRH : Admissible 0.7163436 0.6601618158 7.8209 1.93656 3.011112 (1 / 2) 7 := by
  unfold Admissible
  have := rhs_bounds_GRH.1
  norm_num at this ⊢
  linarith

/-- But not K = 6: "just short of ... on GRH, K = 6". -/
theorem not_admissible_6_GRH :
    ¬ Admissible 0.7163436 0.6601618158 7.8209 1.93656 3.011112 (1 / 2) 6 := by
  unfold Admissible
  have := rhs_bounds_GRH.2
  norm_num at this ⊢
  linarith

end LeanLab.PlattTrudgian2014
