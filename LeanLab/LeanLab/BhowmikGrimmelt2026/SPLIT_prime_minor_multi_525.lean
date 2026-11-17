/-
Split of the prime restricted family step of the bare multi denominator
estimate on the minor arcs.

The family of coefficients is cut by the size of the cutoff N. The cut points are
the square root of X and the midpoint between that square root and X, so the
family is written as three disjoint ranges. On the short range every coefficient
is bounded without any cancellation at all, and the crude bound already fits the
power budget because the range is short. On the two long ranges the coefficient
needs the saving that the minor arc restriction supplies, and the cut separates
the two lengths at which that saving is proved. The three bounds add up, and the
assembly below is complete: nothing beyond the three leaves is assumed.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_minor_bare_multi525

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-! ## The three range leaves -/

/-- LEAF: the short range of the cutoff, where N is at most the square root of X. Every coefficient there is bounded by the power budget without using any cancellation, because the range holds at most a square root of X values of N. -/
theorem prime_minor_multi_525_short {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if N ≤ Nat.sqrt X then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- LEAF: the lower long range of the cutoff, where N is above the square root of X and at most the midpoint between that square root and X. This is the shorter of the two ranges on which the minor arc saving has to be used, and the bound is the full power budget. -/
theorem prime_minor_multi_525_mid {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if Nat.sqrt X < N ∧ N ≤ (Nat.sqrt X + X) / 2 then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- LEAF: the upper long range of the cutoff, where N is above the midpoint between the square root of X and X. This is the longer of the two ranges on which the minor arc saving has to be used, and the bound is the same power budget. -/
theorem prime_minor_multi_525_long {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if (Nat.sqrt X + X) / 2 < N then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-! ## Assembled split -/

/-- A sum over a range splits into the three parts that the two cut points define:
below the first, between the two, and above the second. Each part keeps the full
range as its index set and is switched off outside its own part, so the three
partial sums add without any bookkeeping of intervals. -/
private lemma sum_pieces_525 (X Y Z : ℕ) (hYZ : Y ≤ Z) (f : ℕ → ℝ) :
    (∑ N ∈ Finset.Icc 1 X, (if N ≤ Y then f N else 0)) +
      (∑ N ∈ Finset.Icc 1 X, (if Y < N ∧ N ≤ Z then f N else 0)) +
      (∑ N ∈ Finset.Icc 1 X, (if Z < N then f N else 0)) =
      ∑ N ∈ Finset.Icc 1 X, f N := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N _
  by_cases h1 : N ≤ Y
  · have h2 : ¬ (Y < N) := Nat.not_lt.mpr h1
    have h5 : ¬ (Z < N) := Nat.not_lt.mpr (Nat.le_trans h1 hYZ)
    simp [h1, h2, h5]
  · have h2 : Y < N := Nat.lt_of_not_le h1
    by_cases h3 : N ≤ Z
    · have h4 : ¬ (Z < N) := Nat.not_lt.mpr h3
      simp [h1, h2, h3, h4]
    · have h4 : Z < N := Nat.lt_of_not_le h3
      simp [h1, h2, h3, h4]

/-- The bare multi denominator family on the minor arcs, assembled from the three
range bounds of the cut of the family. The statement is the leaf of the earlier
split unchanged, and the proof uses only the three leaves above. -/
theorem prime_minor_multi_525_split {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ → ∑ N ∈ Finset.Icc 1 X, ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2 ≤ C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := prime_minor_multi_525_short hϕ ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := prime_minor_multi_525_mid hϕ ϑ hϑ hϑ'
  obtain ⟨C₃, hC₃, h₃⟩ := prime_minor_multi_525_long hϕ ϑ hϑ hϑ'
  refine ⟨C₁ + C₂ + C₃, by linarith, ?_⟩
  intro X hX hR
  have hT₁ := h₁ X hX hR
  have hT₂ := h₂ X hX hR
  have hT₃ := h₃ X hX hR
  have hYZ : Nat.sqrt X ≤ (Nat.sqrt X + X) / 2 := by
    have hs : Nat.sqrt X ≤ X := Nat.sqrt_le_self X
    omega
  have hsplit := sum_pieces_525 X (Nat.sqrt X) ((Nat.sqrt X + X) / 2) hYZ
    (fun N => ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2)
  rw [← hsplit]
  calc (∑ N ∈ Finset.Icc 1 X, (if N ≤ Nat.sqrt X then ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2 else 0)) +
        (∑ N ∈ Finset.Icc 1 X,
          (if Nat.sqrt X < N ∧ N ≤ (Nat.sqrt X + X) / 2 then ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2 else 0)) +
        (∑ N ∈ Finset.Icc 1 X, (if (Nat.sqrt X + X) / 2 < N then ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2 else 0))
      ≤ (C₁ * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5) +
          (C₂ * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5) +
          (C₃ * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5) :=
        add_le_add (add_le_add hT₁ hT₂) hT₃
    _ = (C₁ + C₂ + C₃) * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
        ring

end LeanLab.BhowmikGrimmelt2026
