/-
Supply split for the weighted minor family on the range where the minor scale
is at least two. The target is the difference of two sums, so the assembly
bounds it by the full multiplier family with the weight present and by the bare
family, each on the same scale range and each one open leaf below.
All leaves are open; the assembly is complete and uses no sorry.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp451b

namespace LeanLab.BhowmikGrimmelt2026

/-! ## The two multiplier pieces -/

/-- LEAF. Multi-denominator step for the full minor multiplier.
For admissible phi and G and fixed theta strictly between zero and one half, one
nonnegative constant bounds the sum of squared full minor coefficients, weight
present, by the constant times the inverse-scale budget, X cubed and the fifth
power of log X, for every X at least two with X to the theta at least two, every
eta in zero one and ten times R squared at most eta X. This is the first summand
of the difference the target bounds; the bare subtraction is not removed here. -/
theorem minor_weighted_full_multi_leaf451 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ :=
    minor_weighted_multi_denominator451 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ :=
    minor_bare_multi_denominator451 hϕ ϑ hϑ hϑ'
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  intro X hX hR2 η hη hη1 hscale
  have hs := coefficient_split328 (Finset.Icc 1 X)
    (fun N => minorError150 ϕ G X N ϑ η)
    (fun N => minorWeighted328 ϕ G X N ϑ η)
  have hsub : ∀ N ∈ Finset.Icc 1 X,
      minorError150 ϕ G X N ϑ η - minorWeighted328 ϕ G X N ϑ η =
        minorBare328 ϕ X N ϑ := by
    intro N _
    simp only [minorWeighted328]
    ring
  have hsq : (∑ N ∈ Finset.Icc 1 X,
        ‖minorError150 ϕ G X N ϑ η - minorWeighted328 ϕ G X N ϑ η‖ ^ 2) =
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro N hN
    rw [hsub N hN]
  have hA := h₁ X hX hR2 η hη hη1 hscale
  have hB := h₂ X hX hR2
  nlinarith only [hs, hsq, hA, hB]

/-- LEAF. The bare restricted step on the same scale range.
For admissible phi and fixed theta strictly between zero and one half, one
nonnegative constant bounds the sum of squared bare minor coefficients, weight
absent, by the same budget with no eta parameter, for every X at least two with
X to the theta at least two. This is the second summand of the difference, the
same estimate the sibling bare unit leaves open on its own range table. -/
theorem minor_weighted_bare_multi_leaf451 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  exact minor_bare_multi_denominator451 hϕ ϑ hϑ hϑ'

/-! ## The square split, proved -/

/-- The weighted sum of squares is at most twice the bare sum plus the full sum.
The weighted coefficient is the full coefficient minus the bare one, so this is
the two-square inequality applied termwise; no leaf is used. -/
private lemma weighted_sq_le_split_451 (ϕ G : ℝ → ℝ) (X : ℕ) (ϑ η : ℝ) :
    (∑ N ∈ Finset.Icc 1 X, ‖minorWeighted328 ϕ G X N ϑ η‖ ^ 2) ≤
      2 * ((∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) +
        ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2) := by
  have h := coefficient_split328 (Finset.Icc 1 X)
    (fun N => minorWeighted328 ϕ G X N ϑ η) (fun N => minorError150 ϕ G X N ϑ η)
  have hsub : ∀ N ∈ Finset.Icc 1 X,
      minorWeighted328 ϕ G X N ϑ η - minorError150 ϕ G X N ϑ η =
        -minorBare328 ϕ X N ϑ := by
    intro N _
    simp only [minorWeighted328]
    ring
  have hsq : (∑ N ∈ Finset.Icc 1 X,
        ‖minorWeighted328 ϕ G X N ϑ η - minorError150 ϕ G X N ϑ η‖ ^ 2) =
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro N hN
    rw [hsub N hN, norm_neg]
  calc (∑ N ∈ Finset.Icc 1 X, ‖minorWeighted328 ϕ G X N ϑ η‖ ^ 2)
      ≤ 2 * ((∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) +
          ∑ N ∈ Finset.Icc 1 X,
            ‖minorWeighted328 ϕ G X N ϑ η - minorError150 ϕ G X N ϑ η‖ ^ 2) := h
    _ = 2 * ((∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) +
          ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2) := by rw [hsq]

/-! ## Assembly -/

/-- The weighted multi-denominator statement, from the two multiplier pieces. -/
theorem minor_weighted_multi_denominator451_split {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorWeighted328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := minor_weighted_full_multi_leaf451 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := minor_weighted_bare_multi_leaf451 hϕ ϑ hϑ hϑ'
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  intro X hX hR2 η hη hη1 hscale
  have hs := weighted_sq_le_split_451 ϕ G X ϑ η
  have hA := h₁ X hX hR2 η hη hη1 hscale
  have hB := h₂ X hX hR2
  linarith only [hs, hA, hB]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.minor_weighted_full_multi_leaf451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_weighted_bare_multi_leaf451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_weighted_multi_denominator451_split
