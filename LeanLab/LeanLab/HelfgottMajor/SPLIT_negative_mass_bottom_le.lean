import LeanLab.HelfgottMajor.SPLIT_negative_sampling_raw

/-!
Split of `negative_mass_bottom_le` in `LeanLab.HelfgottMajor.SPLIT_negative_sampling_raw`
into three leaves.

The sealed statement bounds the negative half of the middle zero mass restricted to the
short ordinate window between minus three halves and minus one by the single endpoint value
at height one, times the small height budget `0.15 * log q + 3.389`.

The split separates the three jobs the sealed statement does at once. The first leaf is the
convergence prerequisite: the multiplicities of the zeros of the window are summable, so the
constant may be taken out of the sum. The second leaf is the count: twice the multiplicity
sum of the window is within the small height budget. The third leaf is the weight estimate:
on the closed window the Gaussian Mellin norm is at most twice its value at height one, with
a slack factor that the count absorbs.

The partition inside the window, the pointwise comparison, the extraction of the constant
from the sum and the final arithmetic are done in `negative_mass_bottom_le_split`, which has
no sorry of its own. All three leaves are OPEN. No sign condition and no positivity of the
Gaussian Mellin norm is assumed anywhere; a zero multiplicity contributes nothing.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3. The convergence prerequisite. The zeros of the window between minus three
halves and minus one carry finite total multiplicity, so the multiplicity sum of the window
is summable. This is the step that lets a constant be taken out of the sum later; it
estimates no size and uses neither the weight nor the budget. -/
theorem negative_bottom_order_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
      Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := by
  sorry

/-- LEAF 2 of 3. The count. Twice the multiplicity sum of the zeros of the window is at most
the small height budget `0.15 * log q + 3.389`. The factor two is the slack that the weight
estimate of the third leaf spends, so this leaf is easier than the sealed statement, which
carries the budget without that factor. Nothing about the weight enters. -/
theorem negative_bottom_order_sum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) :
    2 * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      0.15 * log (q : ℝ) + 3.389 := by
  sorry

/-- LEAF 3 of 3. The weight. On the closed window between minus three halves and minus one
the Gaussian Mellin norm is at most twice its value at height minus one. This is the
comparability of the weight across the window; it is a pointwise estimate in the ordinate
alone, holds for every smoothing parameter, and bounds no sum. -/
theorem negative_bottom_gaussian_sup_le (δ : ℝ) {t : ℝ} (hlo : -(3 / 2) ≤ t)
    (hhi : t ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- The sealed statement of `negative_mass_bottom_le`, assembled from the three leaves. The
indicator restricts to the same window, the pointwise comparison replaces the weight by its
endpoint value with the slack factor two, the multiplicity sum is summable so the constant
leaves the sum, and the count absorbs the factor. -/
theorem negative_mass_bottom_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ) ≤
      ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) := by
  classical
  have hsummable_mass : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) := by
    apply (Zeros269.low_zero_terms_summable χ δ 1 T hzeros).norm.congr
    intro ρ
    simp [zeroTerm, mellinMassTerm, nsmul_eq_mul]
  have hsummable_weight : Summable (fun ρ : {ρ : ℂ //
      DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) := by
    refine hsummable_mass.congr (fun ρ => ?_)
    have hz := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2
    have hρeq : ρ.val = (1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I := by
      apply Complex.ext <;> simp [hz]
    rw [mellinMassTerm, hρeq]
    simp
  have hpoint : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ ≤
      Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖)) ρ := by
    intro ρ
    by_cases hp : -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1
    · have hmem : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1} := hp
      simp only [Set.indicator_of_mem hmem]
      exact mul_le_mul_of_nonneg_left
        (negative_bottom_gaussian_sup_le δ (le_of_lt hp.1) (le_of_lt hp.2)) (Nat.cast_nonneg _)
    · have hmem : ρ ∉ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1} := hp
      simp only [Set.indicator_of_notMem hmem]
      exact le_rfl
  have hsummable_majorant : Summable (fun ρ : {ρ : ℂ //
      DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
      Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖)) ρ) := by
    have hmul := (negative_bottom_order_summable q χ T).mul_left
      (2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖)
    refine hmul.congr (fun ρ => ?_)
    by_cases hp : ρ ∈ {ρ : {ρ : ℂ //
        DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} |
        -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
    · simp only [Set.indicator_of_mem hp]
      ring
    · simp only [Set.indicator_of_notMem hp, mul_zero]
  have hstep : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ) ≤
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            (2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖)) ρ) :=
    Summable.tsum_le_tsum hpoint (hsummable_weight.indicator _) hsummable_majorant
  have hfactor : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            (2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖)) ρ) =
      (2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖) *
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro ρ
    by_cases hp : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
    · simp only [Set.indicator_of_mem hp]
      ring
    · simp only [Set.indicator_of_notMem hp, mul_zero]
  have hbudget : (2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖) *
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) := by
    have hcount := negative_bottom_order_sum_le q χ hχ T
    have hmul := mul_le_mul_of_nonneg_left hcount
      (norm_nonneg (gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)))
    calc (2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖) *
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) =
        ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ *
          (2 * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)) := by
          ring
      _ ≤ _ := hmul
  calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ)
      ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
              (2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖)) ρ) := hstep
    _ = (2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖) *
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := hfactor
    _ ≤ ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) :=
        hbudget

end LeanLab.HelfgottMajor.Decomp431a
