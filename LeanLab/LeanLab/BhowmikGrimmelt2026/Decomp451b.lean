/-
Supply split for the weighted minor family in P0029 page 27, display 7.8.
The single denominator case uses the proved full multiplier family.
Only the range with at least two denominators remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp451a

namespace LeanLab.BhowmikGrimmelt2026

/-- The actual full minor multiplier has the printed power five below denominator two.
This is the power five consequence of minor_family_single_denominator328. -/
theorem minor_full_single_denominator451 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → (X : ℝ) ^ ϑ < 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, hf⟩ := minor_family_single_denominator328 hϕ hG ϑ hϑ hϑ'
  refine ⟨16 * C, by positivity, ?_⟩
  intro X hX hR2 η hη hη1 hscale
  have hh := mul_le_mul_of_nonneg_left (log_le_sixteen_log5_451 hX)
    (by positivity : 0 ≤ C * (((X : ℝ) ^ ϑ)⁻¹ +
      (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3)
  nlinarith only [hf X hX hR2 η hη hη1 hscale, hh]

/-- Subtraction of the bare coefficient gives the weighted power five bound below two.
Both inputs have clean axioms and use the actual changing smoothing scale. -/
theorem minor_weighted_single_denominator451 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → (X : ℝ) ^ ϑ < 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorWeighted328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := minor_full_single_denominator451 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := minor_bare_single_denominator451 hϕ ϑ
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  intro X hX hR2 η hη hη1 hscale
  have hs : (∑ N ∈ Finset.Icc 1 X, ‖minorWeighted328 ϕ G X N ϑ η‖ ^ 2) ≤
      2 * ((∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) +
        ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2) := by
    calc
      _ ≤ ∑ N ∈ Finset.Icc 1 X,
          2 * (‖minorError150 ϕ G X N ϑ η‖ ^ 2 + ‖minorBare328 ϕ X N ϑ‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro N hN
        have hh := pow_le_pow_left₀ (norm_nonneg
          (minorError150 ϕ G X N ϑ η - minorBare328 ϕ X N ϑ))
          (norm_sub_le (minorError150 ϕ G X N ϑ η) (minorBare328 ϕ X N ϑ)) 2
        change ‖minorError150 ϕ G X N ϑ η - minorBare328 ϕ X N ϑ‖ ^ 2 ≤ _
        nlinarith only [hh, sq_nonneg
          (‖minorError150 ϕ G X N ϑ η‖ - ‖minorBare328 ϕ X N ϑ‖)]
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
  nlinarith only [hs, h₁ X hX hR2 η hη hη1 hscale, h₂ X hX hR2]

/-- LEAF. P0029 page 27, bounded bRhat step in the minor part of display 7.8.
OPEN weighted minor family restricted to R at least two.
The single denominator range is absent and has a separate clean proof.
The full weight remainder and printed logarithm power five are retained. -/
theorem minor_weighted_multi_denominator451 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorWeighted328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- Exact minor_weighted_family328 statement from the two disjoint scale ranges.
CONDITIONAL ON minor_weighted_multi_denominator451. -/
theorem minor_weighted_supply451 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorWeighted328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := minor_weighted_single_denominator451 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := minor_weighted_multi_denominator451 hϕ hG ϑ hϑ hϑ'
  refine ⟨max C₁ C₂, le_trans hC₁ (le_max_left _ _), ?_⟩
  intro X hX η hη hη1 hscale
  by_cases hR2 : (X : ℝ) ^ ϑ < 2
  · apply (h₁ X hX hR2 η hη hη1 hscale).trans
    gcongr
    exact le_max_left _ _
  · apply (h₂ X hX (le_of_not_gt hR2) η hη hη1 hscale).trans
    gcongr
    exact le_max_right _ _

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.minor_full_single_denominator451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_weighted_single_denominator451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_weighted_multi_denominator451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_weighted_supply451
