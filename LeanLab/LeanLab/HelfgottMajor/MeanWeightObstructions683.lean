import LeanLab.HelfgottMajor.PositivePart683
import LeanLab.HelfgottMajor.Decomp269b

/-!
Formal audit of mean only sampling leaves.
At modulus one and height two their right side is negative at zero shift,
while their zero mass sum is nonnegative.
The sealed original statements are unchanged.
This is a defect of the formal splits, with no claim of a paper error.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MeanWeightObstructions683
open Real MeasureTheory Decomp269a Decomp269b

/-- The corresponding sealed mean only sampling leaf is false.
The witness has modulus one, its trivial character, zero shift and height two.
Source audit of book pages 433 and 434, before display 16.26. -/
theorem positive_mass_window_two_le_false :
    ¬ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  intro h
  have hb := h 1 (1 : DirichletCharacter ℂ 1) 0 2 (by norm_num)
  simp only [Nat.cast_one] at hb
  have hleft : (0 : ℝ) ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ)},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm (1 : DirichletCharacter ℂ 1) 0 ρ.val‖) ρ) := by
    apply tsum_nonneg
    intro ρ
    apply Set.indicator_nonneg
    intro u hu
    exact norm_nonneg _
  have hright : (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..(2 : ℝ),
        ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((1 : ℝ) * t / (2 * π)))) < 0 := by
    simp only [one_mul]
    apply mul_neg_of_pos_of_neg (by positivity)
    apply mul_neg_of_pos_of_neg (by positivity)
    exact PositivePart683.signed_gaussian_integral_neg
  exact (not_le_of_gt hright) (hleft.trans hb)

/-- The corresponding sealed mean only sampling leaf is false.
The witness has modulus one, its trivial character, zero shift and height two.
Source audit of book pages 433 and 434, before display 16.26. -/
theorem positive_mass_window_one_high_half_le_false :
    ¬ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  intro h
  have hb := h 1 (1 : DirichletCharacter ℂ 1) 0 2 (by norm_num)
  simp only [Nat.cast_one] at hb
  have hleft : (0 : ℝ) ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ)},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm (1 : DirichletCharacter ℂ 1) 0 ρ.val‖) ρ) := by
    apply tsum_nonneg
    intro ρ
    apply Set.indicator_nonneg
    intro u hu
    exact norm_nonneg _
  have hright : (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..(2 : ℝ),
        ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((1 : ℝ) * t / (2 * π)))) < 0 := by
    simp only [one_mul]
    apply mul_neg_of_pos_of_neg (by positivity)
    apply mul_neg_of_pos_of_neg (by positivity)
    exact PositivePart683.signed_gaussian_integral_neg
  exact (not_le_of_gt hright) (hleft.trans hb)

/-- The corresponding sealed mean only sampling leaf is false.
The witness has modulus one, its trivial character, zero shift and height two.
Source audit of book pages 433 and 434, before display 16.26. -/
theorem positive_mass_window_one_low_half_upper_quarter_le_false :
    ¬ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 9 / 8 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  intro h
  have hb := h 1 (1 : DirichletCharacter ℂ 1) 0 2 (by norm_num)
  simp only [Nat.cast_one] at hb
  have hleft : (0 : ℝ) ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ)},
        Set.indicator {ρ | 9 / 8 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm (1 : DirichletCharacter ℂ 1) 0 ρ.val‖) ρ) := by
    apply tsum_nonneg
    intro ρ
    apply Set.indicator_nonneg
    intro u hu
    exact norm_nonneg _
  have hright : (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..(2 : ℝ),
        ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((1 : ℝ) * t / (2 * π)))) < 0 := by
    simp only [one_mul]
    apply mul_neg_of_pos_of_neg (by positivity)
    apply mul_neg_of_pos_of_neg (by positivity)
    exact PositivePart683.signed_gaussian_integral_neg
  exact (not_le_of_gt hright) (hleft.trans hb)

/-- The corresponding sealed mean only sampling leaf is false.
The witness has modulus one, its trivial character, zero shift and height two.
Source audit of book pages 433 and 434, before display 16.26. -/
theorem positive_mass_window_two_low_window_le_false :
    ¬ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  intro h
  have hb := h 1 (1 : DirichletCharacter ℂ 1) 0 2 (by norm_num)
  simp only [Nat.cast_one] at hb
  have hleft : (0 : ℝ) ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ)},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm (1 : DirichletCharacter ℂ 1) 0 ρ.val‖) ρ) := by
    apply tsum_nonneg
    intro ρ
    apply Set.indicator_nonneg
    intro u hu
    exact norm_nonneg _
  have hright : (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..(2 : ℝ),
        ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((1 : ℝ) * t / (2 * π)))) < 0 := by
    simp only [one_mul]
    apply mul_neg_of_pos_of_neg (by positivity)
    apply mul_neg_of_pos_of_neg (by positivity)
    exact PositivePart683.signed_gaussian_integral_neg
  exact (not_le_of_gt hright) (hleft.trans hb)

/-- The corresponding sealed mean only sampling leaf is false.
The witness has modulus one, its trivial character, zero shift and height two.
Source audit of book pages 433 and 434, before display 16.26. -/
theorem positive_mass_window_two_high_window_le_false :
    ¬ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  intro h
  have hb := h 1 (1 : DirichletCharacter ℂ 1) 0 2 (by norm_num)
  simp only [Nat.cast_one] at hb
  have hleft : (0 : ℝ) ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ)},
        Set.indicator {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm (1 : DirichletCharacter ℂ 1) 0 ρ.val‖) ρ) := by
    apply tsum_nonneg
    intro ρ
    apply Set.indicator_nonneg
    intro u hu
    exact norm_nonneg _
  have hright : (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..(2 : ℝ),
        ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((1 : ℝ) * t / (2 * π)))) < 0 := by
    simp only [one_mul]
    apply mul_neg_of_pos_of_neg (by positivity)
    apply mul_neg_of_pos_of_neg (by positivity)
    exact PositivePart683.signed_gaussian_integral_neg
  exact (not_le_of_gt hright) (hleft.trans hb)

/-- The corresponding sealed mean only sampling leaf is false.
The witness has modulus one, its trivial character, zero shift and height two.
Source audit of book pages 433 and 434, before display 16.26. -/
theorem positive_mass_window_two_low_window_low_half_le_false :
    ¬ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 13 / 8}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  intro h
  have hb := h 1 (1 : DirichletCharacter ℂ 1) 0 2 (by norm_num)
  simp only [Nat.cast_one] at hb
  have hleft : (0 : ℝ) ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ)},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 13 / 8}
          (fun ρ => ‖mellinMassTerm (1 : DirichletCharacter ℂ 1) 0 ρ.val‖) ρ) := by
    apply tsum_nonneg
    intro ρ
    apply Set.indicator_nonneg
    intro u hu
    exact norm_nonneg _
  have hright : (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..(2 : ℝ),
        ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((1 : ℝ) * t / (2 * π)))) < 0 := by
    simp only [one_mul]
    apply mul_neg_of_pos_of_neg (by positivity)
    apply mul_neg_of_pos_of_neg (by positivity)
    exact PositivePart683.signed_gaussian_integral_neg
  exact (not_le_of_gt hright) (hleft.trans hb)

/-- The corresponding sealed mean only sampling leaf is false.
The witness has modulus one, its trivial character, zero shift and height two.
Source audit of book pages 433 and 434, before display 16.26. -/
theorem positive_mass_window_two_low_window_high_half_le_false :
    ¬ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 13 / 8 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  intro h
  have hb := h 1 (1 : DirichletCharacter ℂ 1) 0 2 (by norm_num)
  simp only [Nat.cast_one] at hb
  have hleft : (0 : ℝ) ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ)},
        Set.indicator {ρ | 13 / 8 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm (1 : DirichletCharacter ℂ 1) 0 ρ.val‖) ρ) := by
    apply tsum_nonneg
    intro ρ
    apply Set.indicator_nonneg
    intro u hu
    exact norm_nonneg _
  have hright : (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..(2 : ℝ),
        ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((1 : ℝ) * t / (2 * π)))) < 0 := by
    simp only [one_mul]
    apply mul_neg_of_pos_of_neg (by positivity)
    apply mul_neg_of_pos_of_neg (by positivity)
    exact PositivePart683.signed_gaussian_integral_neg
  exact (not_le_of_gt hright) (hleft.trans hb)

end LeanLab.HelfgottMajor.MeanWeightObstructions683
