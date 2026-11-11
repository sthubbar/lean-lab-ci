/-
A frequency split of the larger denominator family of Decomp461a.
The residual coefficient is first written as the remaining major frequency
integral, with the small denominator multiplier subtracted before any norm or
family sum is taken. The family sum over N is then cut at the square root
cutoff: a short initial range and the long range above it, each carrying the
same fifth logarithm budget.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp461a

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- LEAF. Step one of the reduction. The residual coefficient is exactly the
remaining major frequency integral: the major arc integrand, minus the removed
small denominator multiplier, both under the same smoothing square, the same
unit interval and the same Fourier sign. This is a pointwise identity in N and
carries no norm and no family sum. -/
theorem leaf461_residual_integral {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (X : ℕ) (hX : 2 ≤ X) (N : ℕ) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) (hscale : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X) :
    offRational432 ϕ G X N ϑ η - smallDenCoefficient461 ϕ G X N ϑ η =
      ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
        ({β : ℝ | MajorArc X ((X : ℝ) ^ ϑ) β}.indicator
          (fun β : ℝ => nearContinuous432 G X ((X : ℝ) ^ ϑ) η β -
            continuousModel405 G ((X : ℝ) ^ ϑ)
              (fun q => η * X * q / (X : ℝ) ^ ϑ) β) α -
          smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α)) := by
  sorry

/-- LEAF. Step two, the short initial range. On the frequencies at most the
square root cutoff the remaining major frequency family sum already obeys the
fifth logarithm budget. This is one inequality, on a proper sub-sum of the
family, and the number of retained frequencies is at most the square root of X. -/
theorem leaf461_residual_low_frequency {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → η < (X : ℝ) ^ (ϑ - 1 / 2) →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => 2 * N * N ≤ X),
        ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
          ({β : ℝ | MajorArc X ((X : ℝ) ^ ϑ) β}.indicator
            (fun β : ℝ => nearContinuous432 G X ((X : ℝ) ^ ϑ) η β -
              continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) β) α -
            smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α))‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- LEAF. Step three, the long range. Above the square root cutoff the
remaining major frequency family sum obeys the same fifth logarithm budget.
Here the frequencies are many, so this is the range where the cancellation of
the retained major frequencies has to be used; it is again one inequality on a
proper sub-sum of the family. -/
theorem leaf461_residual_high_frequency {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
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
  sorry

/-- The larger denominator family, assembled from the residual integral
identity and the two frequency ranges. The statement is the sealed one. -/
theorem large_denominator_family461_split {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → η < (X : ℝ) ^ (ϑ - 1 / 2) →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖offRational432 ϕ G X N ϑ η - smallDenCoefficient461 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₀, hC₀, h₀⟩ := leaf461_residual_low_frequency hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₁, hC₁, h₁⟩ := leaf461_residual_high_frequency hϕ hG ϑ hϑ hϑ'
  refine ⟨C₀ + C₁, by linarith, ?_⟩
  intro X hX hR η hη hη1 hsmall hscale
  have hterm : ∀ N ∈ Finset.Icc 1 X,
      ‖offRational432 ϕ G X N ϑ η - smallDenCoefficient461 ϕ G X N ϑ η‖ ^ 2 =
        ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
          ({β : ℝ | MajorArc X ((X : ℝ) ^ ϑ) β}.indicator
            (fun β : ℝ => nearContinuous432 G X ((X : ℝ) ^ ϑ) η β -
              continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) β) α -
            smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α))‖ ^ 2 := by
    intro N _
    rw [leaf461_residual_integral hϕ hG ϑ hϑ X hX N η hη hη1 hscale]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 X)
    (fun N : ℕ => 2 * N * N ≤ X)
    (fun N : ℕ => ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
      ({β : ℝ | MajorArc X ((X : ℝ) ^ ϑ) β}.indicator
        (fun β : ℝ => nearContinuous432 G X ((X : ℝ) ^ ϑ) η β -
          continuousModel405 G ((X : ℝ) ^ ϑ)
            (fun q => η * X * q / (X : ℝ) ^ ϑ) β) α -
        smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α))‖ ^ 2)
  have hlo := h₀ X hX hR η hη hη1 hsmall hscale
  have hhi := h₁ X hX hR η hη hη1 hsmall hscale
  calc
    ∑ N ∈ Finset.Icc 1 X,
        ‖offRational432 ϕ G X N ϑ η - smallDenCoefficient461 ϕ G X N ϑ η‖ ^ 2
        = ∑ N ∈ Finset.Icc 1 X, ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            ({β : ℝ | MajorArc X ((X : ℝ) ^ ϑ) β}.indicator
              (fun β : ℝ => nearContinuous432 G X ((X : ℝ) ^ ϑ) η β -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) β) α -
              smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α))‖ ^ 2 :=
        Finset.sum_congr rfl hterm
    _ = ∑ N ∈ (Finset.Icc 1 X).filter (fun N => 2 * N * N ≤ X),
          ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            ({β : ℝ | MajorArc X ((X : ℝ) ^ ϑ) β}.indicator
              (fun β : ℝ => nearContinuous432 G X ((X : ℝ) ^ ϑ) η β -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) β) α -
              smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α))‖ ^ 2 +
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ 2 * N * N ≤ X),
          ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            ({β : ℝ | MajorArc X ((X : ℝ) ^ ϑ) β}.indicator
              (fun β : ℝ => nearContinuous432 G X ((X : ℝ) ^ ϑ) η β -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) β) α -
              smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α))‖ ^ 2 :=
        hsplit.symm
    _ ≤ C₀ * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 +
          C₁ * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := add_le_add hlo hhi
    _ = (C₀ + C₁) * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf461_residual_integral
#print axioms LeanLab.BhowmikGrimmelt2026.leaf461_residual_low_frequency
#print axioms LeanLab.BhowmikGrimmelt2026.leaf461_residual_high_frequency
#print axioms LeanLab.BhowmikGrimmelt2026.large_denominator_family461_split
