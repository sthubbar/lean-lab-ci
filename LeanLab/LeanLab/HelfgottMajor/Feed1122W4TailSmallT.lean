import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_three_le

/-!
Partial case of the open leaf `positive_mass_window_tail_le` of
`SPLIT_positive_mass_norm_sum_integral`, burst 20261122 wave 4.

The tail leaf bounds the zero mass over ordinates above four by one half of the shifted log weight
integral of the derivative norms over `[1, T]`. The refutation mechanism of windows one and two
does not apply here: the weight `0.15 * log (q * t) + 3.389` is positive for `1 ≤ q` and `1 ≤ t`,
so the right side is never negative.

This file proves the leaf only for `T ≤ 4`, where no zero of the strip with absolute ordinate at
most `T` lies above height four, so the sum vanishes and the bound is the nonnegativity of the
shifted log weight integral, proved on main as `positive_mass_window_three_integral_nonneg`.

The general case is not split, because it looks false for large moduli: see the QUESTION in the
burst notes. The tail drops both hypotheses `hlarge` and `hzeros` of the parent and charges the
tail none of the mean weight integral, which is the main term of P0014 Lemma 4.4.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122W4TailSmallT
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.Decomp269a LeanLab.HelfgottMajor.Decomp269b
  LeanLab.HelfgottMajor.Decomp389b LeanLab.HelfgottMajor.Decomp431a

/-- The tail window above height four is bounded by one half of the shifted log weight integral
when `T ≤ 4`, since then the window is empty. -/
theorem positive_mass_window_tail_le_of_le_four (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) (hT4 : T ≤ 4) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 4 < ρ.val.im}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 2) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  classical
  have hz : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | 4 < ρ.val.im}
        (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ = 0 := by
    intro ρ
    have hle : ρ.val.im ≤ T := le_trans (le_abs_self _) ρ.property.2.2.2
    have h : ¬ (4 < ρ.val.im) := fun hh => by linarith
    simp [h]
  rw [tsum_congr hz, tsum_zero]
  have := positive_mass_window_three_integral_nonneg q δ T hT
  linarith

end LeanLab.HelfgottMajor.Feed1122W4TailSmallT
