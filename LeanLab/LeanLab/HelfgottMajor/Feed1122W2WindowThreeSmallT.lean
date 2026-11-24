import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_three_le

/-!
Partial cases of the two open leaves of `SPLIT_positive_mass_window_three_le`.

`positive_mass_window_three_lower_le` and `positive_mass_window_three_upper_le` are proved here only
in the ranges of the height cut `T` in which the window is empty: for `T ≤ 2` the lower half from
two to three holds no zero of the strip with absolute ordinate at most `T`, and for `T ≤ 3` the
upper half from three to four holds none. In those ranges the sum vanishes and the bound is the
nonnegativity of the shifted log weight integral, leaf 4 of the split, which is proved there.

The general cases are not split here: see the QUESTION notes of burst 20261122. For `δ = 0` and a
modulus with the average number of zeros in the window, the lower half carries about
`0.0328 log q` against a budget of about `0.0276 log q + 0.64` when `T = 3`, so the lower leaf is
expected to fail for very large `q`; and for any `δ` the leaves force every zero in the window to
lie on the critical line once `δ` is large, which is a GRH type statement. AI wrote this Lean code.
-/

namespace LeanLab.HelfgottMajor.Feed1122W2WindowThreeSmallT
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.Decomp269a LeanLab.HelfgottMajor.Decomp269b
  LeanLab.HelfgottMajor.Decomp389b LeanLab.HelfgottMajor.Decomp431a

/-- The lower half of the third window is bounded by a quarter of the budget when `T ≤ 2`, since
then the window is empty. -/
theorem positive_mass_window_three_lower_le_of_le_two (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) (hT2 : T ≤ 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 3}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  classical
  have hz : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 3}
        (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ = 0 := by
    intro ρ
    have hle : ρ.val.im ≤ T := le_trans (le_abs_self _) ρ.property.2.2.2
    have h : ¬ (2 < ρ.val.im ∧ ρ.val.im ≤ 3) := fun hh => by linarith [hh.1]
    simp [h]
  rw [tsum_congr hz, tsum_zero]
  have := positive_mass_window_three_integral_nonneg q δ T hT
  linarith

/-- The upper half of the third window is bounded by a quarter of the budget when `T ≤ 3`, since
then the window is empty. -/
theorem positive_mass_window_three_upper_le_of_le_three (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) (hT3 : T ≤ 3) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 < ρ.val.im ∧ ρ.val.im ≤ 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  classical
  have hz : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | 3 < ρ.val.im ∧ ρ.val.im ≤ 4}
        (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ = 0 := by
    intro ρ
    have hle : ρ.val.im ≤ T := le_trans (le_abs_self _) ρ.property.2.2.2
    have h : ¬ (3 < ρ.val.im ∧ ρ.val.im ≤ 4) := fun hh => by linarith [hh.1]
    simp [h]
  rw [tsum_congr hz, tsum_zero]
  have := positive_mass_window_three_integral_nonneg q δ T hT
  linarith

end LeanLab.HelfgottMajor.Feed1122W2WindowThreeSmallT

