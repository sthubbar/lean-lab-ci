/-
Perelli and Pintz 1993, pages 45 and 46, displays 7 to 13.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
The cited detailed major arc argument is PP1992 pages 359 to 362.
Source http://www.numdam.org/item/CM_1992__82_3_355_0/.
AI wrote the Lean code. Goldbach is open.
The two analytic inputs stay OPEN. The rational partition is proved.
Existing declarations stay sealed.
-/
import LeanLab.Languasco2004.RationalPartition413

namespace LeanLab.Languasco2004.Decomp413b
open Finset Real MeasureTheory Decomp279b
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Page 45 display 7: disjoint rational arcs and translation of
Lebesgue integrals identify the geometric partition. No singular main term
or norm estimate occurs in this statement. -/
theorem major_partition :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ m : ℕ,
      majorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m =
        principalCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m +
        remainderCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m :=
  RationalPartition413.major_partition_from_geometry

/-- LEAF. Page 45 display 8: the principal coefficient after subtracting
the singular main term. This uses the singular series tail and geometric
sums. It contains neither of the two prime sum remainders. -/
theorem principal_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η,
        ‖principalCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m -
          ((Decomp279a.singular m * unweightedCount N (localization N η) m : ℝ) : ℂ)‖ ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by sorry

/-- LEAF. Page 46 displays 9 to 13: the three remainder terms have the
required mean square. The short interval Siegel Walfisz estimate in display 6
controls the first prime sum. The ordinary estimate controls the second.
This statement contains no singular series or principal coefficient. -/
theorem remainder_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η,
        ‖remainderCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by sorry

/-- Pages 45 and 46 displays 7 to 13 give the exact sealed major_bound.
CONDITIONAL ON principal_bound and remainder_bound.
The geometric major_partition has clean axioms. -/
theorem major_bound_from_parts :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η, ‖majorError N η A m‖ ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by
  obtain ⟨e₁, he₁, hsplit⟩ := major_partition
  obtain ⟨e₂, he₂, hprincipal⟩ := principal_bound
  obtain ⟨e₃, he₃, hrem⟩ := remainder_bound
  refine ⟨min e₁ (min e₂ e₃), lt_min he₁ (lt_min he₂ he₃), ?_⟩
  intro η A hη he hA
  obtain ⟨N₁, h₁⟩ := hsplit η A hη (he.trans_le (min_le_left _ _)) hA
  obtain ⟨C₂, N₂, h₂⟩ := hprincipal η A hη
    (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hA
  obtain ⟨C₃, N₃, h₃⟩ := hrem η A hη
    (he.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hA
  refine ⟨2 * (C₂ + C₃), max N₁ (max N₂ N₃), ?_⟩
  intro N hN
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN3 : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hp : ∀ m ∈ window N η, ‖majorError N η A m‖ ^ 2 ≤
      2 * (‖principalCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m -
        ((Decomp279a.singular m * unweightedCount N (localization N η) m : ℝ) : ℂ)‖ ^ 2 +
        ‖remainderCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2) := by
    intro m _
    unfold majorError
    rw [h₁ N hN1 m, add_sub_right_comm]
    exact norm_add_sq _ _
  calc _ ≤ ∑ m ∈ window N η, 2 *
        (‖principalCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m -
          ((Decomp279a.singular m * unweightedCount N (localization N η) m : ℝ) : ℂ)‖ ^ 2 +
          ‖remainderCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2) :=
        sum_le_sum hp
    _ = 2 * ((∑ m ∈ window N η,
        ‖principalCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m -
          ((Decomp279a.singular m * unweightedCount N (localization N η) m : ℝ) : ℂ)‖ ^ 2) +
        ∑ m ∈ window N η,
          ‖remainderCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2) := by
      rw [← mul_sum, sum_add_distrib]
    _ ≤ 2 * (C₂ * windowLength N η * localization N η ^ 2 / Real.log N ^ A +
        C₃ * windowLength N η * localization N η ^ 2 / Real.log N ^ A) := by
      gcongr
      · exact h₂ N hN2
      · exact h₃ N hN3
    _ = _ := by ring

#print axioms major_partition
#print axioms principal_bound
#print axioms remainder_bound
#print axioms major_bound_from_parts
end
end LeanLab.Languasco2004.Decomp413b
