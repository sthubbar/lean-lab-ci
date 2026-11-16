import LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral

/-!
Split of `positive_mass_window_three_le` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral` into four leaves.

The statement being split is the third window of the four way cut of the positive zero mass: it
bounds the multiplicity weighted sum of the Gaussian Mellin norms attached to the zeros whose
ordinate lies above two and at most four, with real part in the open strip, by one half of the
shifted log weight integral of the derivative norms over the height interval `[1, T]`.

The split cuts that window once more, at height three, and charges each half a quarter of the same
shifted log weight integral. A window of height one carries only boundedly many ordinates, so each
half is strictly easier than the window it comes from, and the two quarters add up to the one half
of the statement. A third leaf records that the shifted log weight integral is nonnegative, which
is what settles the case in which the window family is not summable and the sum therefore vanishes,
and a fourth leaf records the pointwise decomposition of the indicator of the window into the
indicators of its two halves.

The assembly is the case split on summability of the window family: in the summable case the
indicator decomposes pointwise, the two quarter bounds are added, and the sum of the two halves of
the summable family is the quarter plus the quarter; in the other case the sum is zero and the
integral is nonnegative. It has no sorry of its own. All four leaves are OPEN.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 4, the pointwise decomposition of the window. The indicator of the height window
from two to four, applied to a zero of the strip below height `T`, is the sum of the indicators of
the two halves of the window, from two to three and from three to four. This is the disjointness
of the two halves; it is an identity of functions on the zero set and uses no analytic input. -/
theorem positive_mass_window_three_indicator_add (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) :
    Set.indicator {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | 2 < ρ.val.im ∧ ρ.val.im ≤ 4}
        (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) =
      Set.indicator {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | 2 < ρ.val.im ∧ ρ.val.im ≤ 3}
          (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) +
        Set.indicator {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | 3 < ρ.val.im ∧ ρ.val.im ≤ 4}
          (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) := by
  classical
  funext ρ
  simp only [Pi.add_apply, Set.indicator_apply]
  by_cases h4 : 2 < ρ.val.im ∧ ρ.val.im ≤ 4
  · by_cases h3 : ρ.val.im ≤ 3
    · simp [h4, h3]
    · simp [h4, h3]
  · have ha : ¬ (2 < ρ.val.im ∧ ρ.val.im ≤ 3) := fun hh => h4 ⟨hh.1, by linarith [hh.2]⟩
    have hb : ¬ (3 < ρ.val.im ∧ ρ.val.im ≤ 4) := fun hh => h4 ⟨by linarith [hh.1], hh.2⟩
    simp [h4, ha, hb]

/-- LEAF 2 of 4, the lower half of the window. The multiplicity weighted sum of the Gaussian Mellin
norms over the zeros whose ordinate lies above two and at most three is at most a quarter of the
shifted log weight integral over the height interval, the window family being assumed summable.
This half of the window is one height unit tall, so it carries only boundedly many ordinates, and
it is charged a quarter of the budget rather than the whole of it. -/
theorem positive_mass_window_three_lower_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 3}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  sorry

/-- LEAF 3 of 4, the upper half of the window. The multiplicity weighted sum of the Gaussian Mellin
norms over the zeros whose ordinate lies above three and at most four is at most a quarter of the
same shifted log weight integral over the height interval, the window family being assumed
summable. This is the other height unit tall half of the window, charged the other quarter. The
two quarters together are the one half of the statement being split. -/
theorem positive_mass_window_three_upper_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 < ρ.val.im ∧ ρ.val.im ≤ 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  sorry

/-- LEAF 4 of 4, nonnegativity of the budget. The shifted log weight integral over the height
interval is nonnegative: on `[1, T]` with `1 ≤ T` and `1 ≤ q` the modulus times the height is at
least one, so its logarithm is nonnegative, and the norm of the derivative value is nonnegative.
This is the estimate that makes the statement hold in the case in which the window family is not
summable, where the sum is zero. -/
theorem positive_mass_window_three_integral_nonneg (q : ℕ) [NeZero q] (δ T : ℝ)
    (hT : 1 ≤ T) :
    0 ≤ ∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389) := by
  refine intervalIntegral.integral_nonneg hT (fun t ht => ?_)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have h : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast h
  have ht1 : (1 : ℝ) ≤ t := ht.1
  have hqt : (1 : ℝ) ≤ (q : ℝ) * t := by
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (q : ℝ) * t := mul_le_mul hq1 ht1 (by norm_num) (by linarith)
  have hlog : 0 ≤ log ((q : ℝ) * t) := log_nonneg hqt
  have hw : 0 ≤ 0.15 * log ((q : ℝ) * t) + 3.389 := by linarith
  exact mul_nonneg (norm_nonneg _) hw

/-- The two halves of the window are bounded by a quarter each and add up to the one half of the
statement, and the case in which the window family is not summable is settled by the vanishing of
the sum against the nonnegative budget. -/
theorem positive_mass_window_three_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 2) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  classical
  by_cases hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)
  · have hs1 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
          Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 3}
            (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := by
      refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) hs
      · by_cases h : 2 < ρ.val.im ∧ ρ.val.im ≤ 3
        · simp [h]
        · simp [h]
      · by_cases h4 : 2 < ρ.val.im ∧ ρ.val.im ≤ 4
        · by_cases h1 : 2 < ρ.val.im ∧ ρ.val.im ≤ 3
          · simp [h4, h1]
          · have h3 : ¬ (ρ.val.im ≤ 3) := fun hh => h1 ⟨h4.1, hh⟩
            simp [h4, h1, h3, norm_nonneg]
        · have h1 : ¬ (2 < ρ.val.im ∧ ρ.val.im ≤ 3) := fun hh => h4 ⟨hh.1, by linarith [hh.2]⟩
          simp [h4, h1]
    have hs2 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
          Set.indicator {ρ | 3 < ρ.val.im ∧ ρ.val.im ≤ 4}
            (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := by
      refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) hs
      · by_cases h : 3 < ρ.val.im ∧ ρ.val.im ≤ 4
        · simp [h]
        · simp [h]
      · by_cases h4 : 2 < ρ.val.im ∧ ρ.val.im ≤ 4
        · by_cases h2 : 3 < ρ.val.im ∧ ρ.val.im ≤ 4
          · simp [h4, h2]
          · have h3 : ¬ (3 < ρ.val.im) := fun hh => h2 ⟨hh, h4.2⟩
            simp [h4, h2, h3, norm_nonneg]
        · have h2 : ¬ (3 < ρ.val.im ∧ ρ.val.im ≤ 4) := fun hh => h4 ⟨by linarith [hh.1], hh.2⟩
          simp [h4, h2]
    have hsplit :
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 4}
              (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
          ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            (Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 3}
                (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ +
              Set.indicator {ρ | 3 < ρ.val.im ∧ ρ.val.im ≤ 4}
                (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) :=
      tsum_congr (fun ρ => congrFun (positive_mass_window_three_indicator_add q χ δ T) ρ)
    rw [hsplit, Summable.tsum_add hs1 hs2]
    linarith [positive_mass_window_three_lower_le q χ δ T hT hs,
      positive_mass_window_three_upper_le q χ δ T hT hs]
  · rw [tsum_eq_zero_of_not_summable hs]
    linarith [positive_mass_window_three_integral_nonneg q δ T hT]

end LeanLab.HelfgottMajor.Decomp431a
