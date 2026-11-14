/-
Split of the weighted multi denominator minor family estimate `minor_weighted_multi525`
of Decomp525a into its two multiplier pieces.

The weighted minor coefficient is the full minor coefficient minus the bare one, so the
termwise square split bounds its family second moment by twice the sum of the two
component family budgets, each at the same power part. Each component is one open leaf
below; the assembly is complete and uses no sorry.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp525a

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- LEAF. The bare minor coefficient family on the range where the minor scale is at
least two: one nonnegative constant bounds the sum of its squared coefficients by the
inverse scale power part, X cubed and the fifth power of log X, for every X at least two
with X to the theta at least two. This is the multiplier free summand of the difference
the target bounds. -/
theorem split_leaf_bare_multi525 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare525 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- LEAF. The full minor coefficient family on the same range, with the weight
transform present as the factor one minus bRhat: one nonnegative constant bounds the
sum of its squared coefficients by the same inverse scale power part, X cubed and the
fifth power of log X, for every X at least two with X to the theta at least two, every
eta in zero one and the scale condition ten R squared at most eta X. The bare
subtraction is not removed here, so this is the other summand of the difference the
target bounds. -/
theorem split_leaf_full_multi525 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- The weighted sum of squares is at most twice the bare sum plus the full sum.
The weighted coefficient is the full coefficient minus the bare one, so this is the
termwise square inequality; no leaf is used. -/
private lemma weighted_sq_le_split_525 (ϕ G : ℝ → ℝ) (X : ℕ) (ϑ η : ℝ) :
    (∑ N ∈ Finset.Icc 1 X, ‖minorWeighted525 ϕ G X N ϑ η‖ ^ 2) ≤
      2 * ((∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) +
        ∑ N ∈ Finset.Icc 1 X, ‖minorBare525 ϕ X N ϑ‖ ^ 2) := by
  have h := coefficient_split525 (Finset.Icc 1 X)
    (fun N => minorWeighted525 ϕ G X N ϑ η) (fun N => minorError150 ϕ G X N ϑ η)
  have hsub : ∀ N ∈ Finset.Icc 1 X,
      minorWeighted525 ϕ G X N ϑ η - minorError150 ϕ G X N ϑ η =
        -minorBare525 ϕ X N ϑ := by
    intro N _
    simp only [minorWeighted525]
    ring
  have hsq : (∑ N ∈ Finset.Icc 1 X,
        ‖minorWeighted525 ϕ G X N ϑ η - minorError150 ϕ G X N ϑ η‖ ^ 2) =
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare525 ϕ X N ϑ‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro N hN
    rw [hsub N hN, norm_neg]
  calc (∑ N ∈ Finset.Icc 1 X, ‖minorWeighted525 ϕ G X N ϑ η‖ ^ 2)
      ≤ 2 * ((∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) +
          ∑ N ∈ Finset.Icc 1 X,
            ‖minorWeighted525 ϕ G X N ϑ η - minorError150 ϕ G X N ϑ η‖ ^ 2) := h
    _ = 2 * ((∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) +
          ∑ N ∈ Finset.Icc 1 X, ‖minorBare525 ϕ X N ϑ‖ ^ 2) := by rw [hsq]

/-- The weighted multi denominator minor family estimate, from the two multiplier
pieces. The constant is twice the sum of the two leaf constants. -/
theorem minor_weighted_multi525_split {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorWeighted525 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := split_leaf_full_multi525 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := split_leaf_bare_multi525 hϕ ϑ hϑ hϑ'
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  intro X hX hR2 η hη hη1 hscale
  have hs := weighted_sq_le_split_525 ϕ G X ϑ η
  have hA := h₁ X hX hR2 η hη hη1 hscale
  have hB := h₂ X hX hR2
  nlinarith only [hs, hA, hB]

end LeanLab.BhowmikGrimmelt2026
