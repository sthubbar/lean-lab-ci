import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_le

/-!
Split of `positive_mass_window_one_low_half_le` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_le.lean` into four leaves.

The statement being split bounds the multiplicity weighted sum of the Gaussian Mellin norms of the
zeros of a Dirichlet `L`-function in the strip `0 < re < 1` and below height `T`, restricted to the
lowest ordinate band of the positive range, above one and at most five quarters, by a quarter of
the mean weight integral against the log weight, plus the value at height one against the shifted
log weight at one.

The split separates the two things the bound needs. First, the band family has to converge at all:
the statement is a sum over every zero in the strip below height `T` and carries no hypothesis on
the zeros, so nothing in the closure makes that family summable, and a family that does not
converge has no additivity to offer over a cut of the ordinate range. Second, the band
`(1, 5 / 4]` is cut at nine eighths and each half is charged an eighth of the mean weight
integral; the value at height one is charged in full to the lower half, which is the piece that
carries the smaller ordinates. An eighth plus an eighth is the quarter of the statement being
split, and the two halves carry at most the whole of the band's ordinates while each of them is
set against half of what the whole band is allowed, which is what makes both window leaves
strictly easier than the statement being split.

The assembly is exactly three ingredients: the identity of sums over the two halves, which is
where the convergence leaf is spent, and the addition of the two window bounds. It has no sorry
of its own. The window identity is proved in this file; the convergence leaf and the two window
bounds are OPEN.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 4, the convergence of the band family. The nonnegative family of the Gaussian
Mellin norms at the zeros in the strip below height `T` is summable. Below a fixed height the
ordinates lie in a compact rectangle and the zeros are isolated there, so only finitely many of
them carry weight; this is the input the window identity below needs, and it is stated on its own
because a sum of the norms over a family that does not converge has no additivity to offer over a
cut of the ordinate range. -/
theorem positive_mass_window_one_low_half_norm_summable (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) := by
  classical
  exact positive_mass_window_one_norm_summable q χ δ T hT

/-- LEAF 2 of 4, the window decomposition. Given the convergence of the band family, the sum over
the ordinates above one and at most five quarters is the sum over the ordinates above one and at
most nine eighths, plus the sum over the ordinates above nine eighths and at most five quarters.
As a statement this is the additivity of the zero sum over a disjoint cut of the band, and it is
the only place where the convergence leaf is spent. The pointwise identity of the two indicators is
elementary and the additivity of the summable family follows from the convergence leaf, so this
leaf is proved here rather than left open. -/
theorem positive_mass_window_one_low_half_window_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖)) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 9 / 8}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 9 / 8 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)) := by
  have hkey : ∀ (x v : ℝ), (if (1 : ℝ) < x ∧ x ≤ 5 / 4 then v else 0) =
      (if (1 : ℝ) < x ∧ x ≤ 9 / 8 then v else 0) +
        (if (9 / 8 : ℝ) < x ∧ x ≤ 5 / 4 then v else 0) := by
    intro x v
    by_cases h1 : (1 : ℝ) < x
    · by_cases h2 : x ≤ 5 / 4
      · by_cases h3 : x ≤ 9 / 8
        · have h4 : ¬ ((9 / 8 : ℝ) < x) := not_lt.mpr h3
          simp [h1, h2, h3, h4]
        · have h3' : (9 / 8 : ℝ) < x := lt_of_not_ge h3
          simp [h1, h2, h3, h3']
      · have h4 : ¬ ((9 / 8 : ℝ) < x ∧ x ≤ 5 / 4) := fun h => h2 h.2
        have h6 : ¬ (x ≤ 9 / 8) := by
          have h7 : (5 / 4 : ℝ) < x := lt_of_not_ge h2
          linarith
        simp [h1, h2, h4, h6]
    · have h4 : ¬ ((1 : ℝ) < x ∧ x ≤ 9 / 8) := fun h => h1 h.1
      have h5 : ¬ ((9 / 8 : ℝ) < x ∧ x ≤ 5 / 4) := fun h => h1 (by linarith [h.1])
      simp [h1, h4, h5]
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ =
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 9 / 8}
            (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ +
          Set.indicator {ρ | 9 / 8 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
            (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ := by
    intro ρ
    simpa only [Set.indicator, Set.mem_ofPred_eq] using
      hkey ρ.val.im ‖mellinMassTerm χ δ ρ.val‖
  refine (tsum_congr hpt).trans ?_
  exact Summable.tsum_add (hs.indicator _) (hs.indicator _)

/-- LEAF 3 of 4, the lower half of the band, with the endpoint. The multiplicity weighted sum of
the Gaussian Mellin norms over the zeros whose ordinate lies above one and at most nine eighths is
at most one eighth of the mean weight integral over the height interval, plus the value at height
one against the shifted log weight at one. This half carries the smallest ordinates of the band,
so it is the one that pays the value at height one, and it is charged only an eighth of the mean
weight integral, half of the share the whole band is allowed. -/
theorem positive_mass_window_one_low_half_lower_quarter_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 9 / 8}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) := by
  sorry

/-- LEAF 4 of 4, the upper half of the band. The multiplicity weighted sum of the Gaussian Mellin
norms over the zeros whose ordinate lies above nine eighths and at most five quarters is at most
one eighth of the mean weight integral over the height interval. This half carries no endpoint
term and is charged the same eighth of the mean weight integral, so the two halves together spend
only the quarter of the statement being split. -/
theorem positive_mass_window_one_low_half_upper_quarter_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 9 / 8 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  sorry

/-- The two halves add up to the bound of `positive_mass_window_one_low_half_le`. The band
`(1, 5 / 4]` cuts at nine eighths into two disjoint halves, the convergence leaf makes that cut an
identity of sums, the two shares of one eighth each add up to the quarter of the statement being
split, and the value at height one is carried by the lower half, so the two right hand sides add
up to the right hand side of the statement being split. -/
theorem positive_mass_window_one_low_half_le_split
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) := by
  classical
  have hs := positive_mass_window_one_low_half_norm_summable q χ δ T hT
  refine (le_of_eq (positive_mass_window_one_low_half_window_split q χ δ T hT hs)).trans ?_
  refine (add_le_add
    (positive_mass_window_one_low_half_lower_quarter_le q χ δ T hT)
    (positive_mass_window_one_low_half_upper_quarter_le q χ δ T hT)).trans (le_of_eq ?_)
  ring

end LeanLab.HelfgottMajor.Decomp431a
