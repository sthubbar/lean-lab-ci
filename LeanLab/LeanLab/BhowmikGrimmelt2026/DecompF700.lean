/-
Split of leaf461_residual_high_frequency for FREE-nv-minimax2 task700.
The high frequency range N with ¬ 2*N*N ≤ X is bounded by splitting into
a cardinality leaf and a pointwise integral leaf. The assembly combines
them with a one line sum bound.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_large_denominator_family461

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- LEAF. Step one of the high frequency split. The number of frequencies N in
[1,X] with ¬ 2*N*N ≤ X is at most X. This is one cardinality inequality on
the filtered finset. -/
theorem leaf461_high_freq_card (X : ℕ) :
    ((Finset.Icc 1 X).filter (fun N => ¬ 2 * N * N ≤ X)).card ≤ X := by
  sorry

/-- LEAF. Step two of the high frequency split. Each individual high frequency
integral term has squared norm bounded by C * η^4 * X^2 * (log X)^5. This is
one pointwise inequality, strictly easier than the summed target because it
bounds a single term instead of the whole family. -/
theorem leaf461_high_freq_pointwise {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → η < (X : ℝ) ^ (ϑ - 1 / 2) →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∀ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ 2 * N * N ≤ X),
        ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
          ({β : ℝ | MajorArc X ((X : ℝ) ^ ϑ) β}.indicator
            (fun β : ℝ => nearContinuous432 G X ((X : ℝ) ^ ϑ) η β -
              continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) β) α -
            smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α))‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 2 * Real.log X ^ 5 := by
  sorry

/-- LEAF. Step three of the high frequency split. The logarithm of a natural
number at least 2 is nonnegative, so it can be used in monotonicity steps
without sign issues. This is one elementary real inequality. -/
theorem leaf461_high_freq_log_nonneg (X : ℕ) (hX : 2 ≤ X) : 0 ≤ Real.log X := by
  sorry

/-- The high frequency residual sum assembled from the cardinality leaf and
the pointwise leaf. The statement is copied character for character from
leaf461_residual_high_frequency. -/
theorem leaf461_residual_high_frequency_F700 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → η < (X : ℝ) ^ (ϑ - 1 / 2) →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ 2 * N * N ≤ X),
        ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
          ({β : ℝ | MajorArc X ((X : ℝ) ^ ϑ) β}.indicator
            (fun β : ℝ => nearContinuous432 G X ((X : ℝ) ^ ϑ) η β -
              continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) β) α -
            smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α))‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := leaf461_high_freq_pointwise hϕ hG ϑ hϑ hϑ'
  refine ⟨C₁, hC₁, ?_⟩
  intro X hX hR η hη hη1 hsmall hscale
  have hcard := leaf461_high_freq_card X
  have hlog := leaf461_high_freq_log_nonneg X hX
  calc
    ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ 2 * N * N ≤ X),
        ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
          ({β : ℝ | MajorArc X ((X : ℝ) ^ ϑ) β}.indicator
            (fun β : ℝ => nearContinuous432 G X ((X : ℝ) ^ ϑ) η β -
              continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) β) α -
            smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α))‖ ^ 2
        ≤ ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ 2 * N * N ≤ X),
          C₁ * η ^ 4 * (X : ℝ) ^ 2 * Real.log X ^ 5 := by
      apply Finset.sum_le_sum
      intro N hN
      exact h₁ X hX hR η hη hη1 hsmall hscale N hN
    _ = ((Finset.Icc 1 X).filter (fun N => ¬ 2 * N * N ≤ X)).card *
        (C₁ * η ^ 4 * (X : ℝ) ^ 2 * Real.log X ^ 5) := by
      simp [Finset.sum_const, smul_eq_mul]
    _ ≤ (X : ℝ) * (C₁ * η ^ 4 * (X : ℝ) ^ 2 * Real.log X ^ 5) := by
      gcongr
      exact mod_cast hcard
    _ = C₁ * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
      ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf461_high_freq_card
#print axioms LeanLab.BhowmikGrimmelt2026.leaf461_high_freq_pointwise
#print axioms LeanLab.BhowmikGrimmelt2026.leaf461_high_freq_log_nonneg
#print axioms LeanLab.BhowmikGrimmelt2026.leaf461_residual_high_frequency_F700
