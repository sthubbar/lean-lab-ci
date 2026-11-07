/-
A split of the continuous tail family bound into three leaves plus an assembly.

The major arc integral for the continuous tail is partitioned by frequency region:
the arcs of denominator one, where the nearest integer representative is the selected
rational, and the remaining major arcs, where the selected rational has denominator at
least two. The leaves are (1) the reduction of the coefficient to the sum of the two
region pieces, (2) the family bound on the denominator one region, and (3) the family
bound on the remaining major arcs. The assembly combines them with the two term split
of a finite family of squared norms and the absorption of the logarithm power.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp405a

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory
open scoped FourierTransform

/-- LEAF. Step 1, the reduction: the continuous tail coefficient is exactly the sum of
its two frequency region pieces, the major arcs whose centre is an integer and the
remaining major arcs. This is the indicator identity for the major arc set together with
the interval integrability of both pieces; no estimate enters it. -/
theorem leaf_region_split405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    {X : ℕ} (hX : 2 ≤ X) (N : ℕ) (ϑ : ℝ) (hϑ : 0 < ϑ) {η : ℝ} (hη : 0 < η) :
    continuousTail405 ϕ G X N ϑ η =
      (∫ α in (0 : ℝ)..1,
        ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
          {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}).indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
              continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α) +
      (∫ α in (0 : ℝ)..1,
        ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
          {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}ᶜ).indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
              continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α) := by
  sorry

/-- LEAF. Step 2, the denominator one region: on the major arcs whose centre is an
integer the mean square over the smoothing family of the continuous tail coefficient is
of order eta to the fourth times X cubed times the fifth power of the logarithm. Only the
region near the integers enters, so the rational pair count of the remaining arcs is not
incurred here. -/
theorem leaf_denominator_one405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
            {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}).indicator
            (fun α => Sphi ϕ N α ^ 2 *
              (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- LEAF. Step 3, the remaining major arcs: on the major arcs whose centre is not an
integer the same mean square over the smoothing family is of order eta to the fourth
times X cubed times the fifth power of the logarithm. This region carries the rational
centres of denominator at least two together with the full rational sum of the model, so
the pair count and the separation of distinct centres are needed here. -/
theorem leaf_other_arcs405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
            {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}ᶜ).indicator
            (fun α => Sphi ϕ N α ^ 2 *
              (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- The continuous tail family bound assembled from the three leaves above. -/
theorem continuous_tail_family405_split {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖continuousTail405 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := leaf_denominator_one405 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := leaf_other_arcs405 hϕ hG ϑ hϑ hϑ'
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hsplit := coefficient_split328 (Finset.Icc 1 X)
    (fun N => continuousTail405 ϕ G X N ϑ η)
    (fun N => ∫ α in (0 : ℝ)..1,
      ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
        {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}).indicator
        (fun α => Sphi ϕ N α ^ 2 *
          (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
            continuousModel405 G ((X : ℝ) ^ ϑ)
              (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α)
  have hsub : ∀ N ∈ Finset.Icc 1 X,
      ‖continuousTail405 ϕ G X N ϑ η -
        (∫ α in (0 : ℝ)..1,
          ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
            {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}).indicator
            (fun α => Sphi ϕ N α ^ 2 *
              (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α)‖ ^ 2 =
        ‖(∫ α in (0 : ℝ)..1,
          ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
            {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}ᶜ).indicator
            (fun α => Sphi ϕ N α ^ 2 *
              (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α)‖ ^ 2 := by
    intro N _
    rw [leaf_region_split405 hϕ hG hX N ϑ hϑ hη]
    rw [add_sub_cancel_left]
  rw [Finset.sum_congr rfl hsub] at hsplit
  have hb₁ := h₁ X hX η hη hη1 hscale
  have hb₂ := h₂ X hX η hη hη1 hscale
  nlinarith only [hsplit, hb₁, hb₂]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_region_split405
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_denominator_one405
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_other_arcs405
#print axioms LeanLab.BhowmikGrimmelt2026.continuous_tail_family405_split
