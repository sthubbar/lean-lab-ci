import LeanLab.HelfgottMajor.Decomp269b
import LeanLab.HelfgottMajor.HalfMoment389
import LeanLab.HelfgottMajor.ZeroCount1623

/-!
P0014 Lemma 4.4, page 39, very low zeros.
The zero count and the scalar Gaussian half moment are independent inputs.
The sealed Decomp269b leaf is unchanged.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp389a
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- Multiplicity count below height 1, inside the height T indexing set of page 39. -/
noncomputable def veryLowCountTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}) : ℝ :=
  Set.indicator {ρ | |ρ.val.im| ≤ 1}
    (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ

/-- LEAF. Page 39, the N of 1 paragraph, from displays 4.25 and 4.26 on pages 37 and 38.
This counts multiplicities and makes no assertion about Mellin values or the critical line.
-/
theorem very_low_zero_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) ∧
      (∑' ρ, veryLowCountTerm χ T ρ) ≤ 0.819 * log q + 16.8 := by
  exact ⟨ZeroCount1623.summable_zeroIdx χ T (veryLowCountTerm χ T),
    ZeroCount1623.very_low_count χ hχ T hT⟩

/-- Page 43, display 4.42, the scalar Gaussian half moment numerical bound.
This has no zero sum, character, shift or height parameter.
-/
theorem gaussian_half_moment_bound :
    (∫ t in Set.Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2)) ≤
      2.15581 := by
  exact HalfMoment389.gaussian_half_moment_bound

/-- Display 4.30 on page 39 specialized to the critical line.
CONDITIONAL ON the scalar half moment inequality, supplied explicitly here.
-/
theorem mellin_critical_norm_le (δ : ℝ) (s : ℂ) (hs : s.re = 1 / 2)
    (hhalf : (∫ t in Set.Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2)) ≤
      2.15581) :
    ‖gaussianMellin δ s‖ ≤ 2.15581 := by
  have h := Gaussian269.mellin_norm_le δ s
  rw [hs] at h
  exact h.trans hhalf

/-- The weighted comparison in the very low zero paragraph on page 39.
CONDITIONAL ON hzeros, count summability and the pointwise Mellin bound.
-/
theorem very_low_mass_le_count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcount : Summable (veryLowCountTerm χ T))
    (hpoint : ∀ s : ℂ, s.re = 1 / 2 → ‖gaussianMellin δ s‖ ≤ 2.15581) :
    veryLowMass χ δ T ≤ 2.15581 * ∑' ρ, veryLowCountTerm χ T ρ := by
  classical
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) := by
    apply (Zeros269.low_zero_terms_summable χ δ 1 T hzeros).norm.congr
    intro ρ
    simp [zeroTerm, mellinMassTerm, nsmul_eq_mul]
  unfold veryLowMass
  rw [← tsum_mul_left]
  apply (hm.indicator _).tsum_le_tsum _ (hcount.mul_left 2.15581)
  intro ρ
  by_cases h : |ρ.val.im| ≤ 1
  · simp only [veryLowCountTerm, Set.indicator, Set.mem_ofPred_eq, h, ite_true, mellinMassTerm]
    have hz := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hpoint ρ.val hz)
      (Nat.cast_nonneg (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val))
  · simp [veryLowCountTerm, Set.indicator, h]

/-- Exactly Decomp269b.very_low_mass_bound, from the two independent smaller leaves.
This assembly has no sorry of its own and remains dependent on those OPEN leaves.
-/
theorem very_low_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    veryLowMass χ δ T ≤ 2.15581 * (0.819 * log q + 16.8) := by
  obtain ⟨hcount, hbudget⟩ := very_low_zero_count q χ hχ T hT
  exact (very_low_mass_le_count χ δ T hzeros hcount
    (fun s hs => mellin_critical_norm_le δ s hs gaussian_half_moment_bound)).trans
      (mul_le_mul_of_nonneg_left hbudget (by norm_num))

end LeanLab.HelfgottMajor.Decomp389a
