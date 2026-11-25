import LeanLab.HelfgottMajor.Decomp269b

/-!
Leaves for Decomp269b.very_low_mass_bound, P0014 Lemma 4.4, page 39.
The paper bounds each critical line Mellin norm by the Gaussian half moment 2.15581
and multiplies by the count of zeros below height 1.
The assembly below derives the parent statement from those two pieces.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269bLeavesVeryLow
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- LEAF: P0014 page 39 with display 4.42 on page 43, the pointwise Mellin bound on the
critical line. Class MEDIUM. P0014 display 4.42: for real part 1/2 the Gaussian Mellin
norm is at most the integral of exp of minus t squared over 2 times t to the minus 1/2,
which equals 2 to the minus 3/4 times Gamma of 1/4, about 2.15581, for every delta. -/
theorem gaussianMellin_half_line_le (δ : ℝ) (ρ : ℂ) (hre : ρ.re = 1 / 2) :
    ‖gaussianMellin δ ρ‖ ≤ 2.15581 :=
  SplitGaussian123.mellin_critical_norm_le δ ρ hre

/-- LEAF: P0014 page 39, displays 4.25, 4.26 and 4.30, the count of zeros of height at
most 1 with multiplicity. Class HARD. P0014 display 4.30: N of 1 and chi is at most
0.819 log q plus 16.8 for primitive chi; summability is part of the statement. -/
theorem very_low_count_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
      Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      0.819 * log q + 16.8 :=
  -- The index type is ZeroCount1623.ZeroIdx, finite by stripZeros_finite, so summability
  -- is unconditional. The bound is ZeroCount1623.very_low_count, CONDITIONAL ON the shared
  -- lab leaf ZeroCount1623.book_zero_count.
  ⟨ZeroCount1623.summable_zeroIdx χ T _, ZeroCount1623.very_low_count χ hχ T hT⟩

/-- Exactly Decomp269b.very_low_mass_bound, assembled from the two leaves above. -/
theorem very_low_mass_bound_of_leaves (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    veryLowMass χ δ T ≤ 2.15581 * (0.819 * log q + 16.8) := by
  classical
  obtain ⟨hs, hc⟩ := very_low_count_bound q χ hχ T hT
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) := by
    apply (Zeros269.low_zero_terms_summable χ δ 1 T hzeros).norm.congr
    intro ρ
    simp [zeroTerm, mellinMassTerm, nsmul_eq_mul]
  unfold veryLowMass
  calc _ ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, 2.15581 *
        Set.indicator {ρ | |ρ.val.im| ≤ 1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ := by
        apply (hm.indicator _).tsum_le_tsum _ (hs.mul_left _)
        intro ρ
        by_cases h : |ρ.val.im| ≤ 1
        · have hre := hzeros ρ.val ρ.2.1 ρ.2.2.1 ρ.2.2.2.1 ρ.2.2.2.2
          have hb := gaussianMellin_half_line_le δ ρ.val hre
          simp only [Set.indicator, Set.mem_setOf_eq, h, if_true, mellinMassTerm]
          have h0 : (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) :=
            Nat.cast_nonneg _
          nlinarith
        · simp [Set.indicator, h]
    _ = 2.15581 * ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | |ρ.val.im| ≤ 1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ :=
        tsum_mul_left
    _ ≤ _ := by linarith

end LeanLab.HelfgottMajor.Decomp269bLeavesVeryLow

