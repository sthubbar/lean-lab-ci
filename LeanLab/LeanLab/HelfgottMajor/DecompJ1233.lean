import LeanLab.HelfgottMajor.Decomp269b
import LeanLab.HelfgottMajor.Decomp389a
import LeanLab.HelfgottMajor.HalfMoment389

/-!
Decomposition of very_low_mass_bound.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DecompJ1233
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389a

/-- LEAF. The scalar Gaussian half moment. -/
theorem leaf_gaussian_half_moment_bound :
    (∫ t in Set.Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2)) ≤ 2.15581 := by
  exact HalfMoment389.gaussian_half_moment_bound

/-- LEAF. The critical line Mellin bound. -/
theorem leaf_mellin_critical_norm_le (δ : ℝ) (s : ℂ) (hs : s.re = 1 / 2) :
    ‖gaussianMellin δ s‖ ≤ 2.15581 := by
  have h := Gaussian269.mellin_norm_le δ s
  rw [hs] at h
  exact h.trans HalfMoment389.gaussian_half_moment_bound

/-- LEAF. The zero count paragraph on page 39. -/
theorem leaf_very_low_zero_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) ∧
      (∑' ρ, veryLowCountTerm χ T ρ) ≤ 0.819 * log q + 16.8 := by
  exact Decomp389a.very_low_zero_count q χ hχ T hT

/-- The target theorem very_low_mass_bound. -/
theorem very_low_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    veryLowMass χ δ T ≤ 2.15581 * (0.819 * log q + 16.8) := by
  obtain ⟨hcount, hbudget⟩ := leaf_very_low_zero_count q χ hχ T hT
  exact (very_low_mass_le_count χ δ T hzeros hcount
    (fun s hs => leaf_mellin_critical_norm_le δ s hs)).trans
      (mul_le_mul_of_nonneg_left hbudget (by norm_num))

end LeanLab.HelfgottMajor.DecompJ1233
