import LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral

/-!
Split of `positive_mass_window_one_le` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral` into four leaves.

The statement being split bounds the nonnegative, multiplicity weighted sum of the Gaussian
Mellin norms attached to the positive zeros of a Dirichlet `L`-function in the strip
`0 < re < 1` and below height `T`, restricted to the lowest ordinate band of the positive range,
above one and at most three halves, by half of the critical line norm integral against the mean
weight on the height interval `[1, T]`, plus the value at height one against the shifted log
weight at one.

The split separates the two things the bound needs. First, the band family has to converge at
all: the statement is a sum over every zero in the strip below height `T` and carries no
hypothesis on the zeros, so nothing in the closure makes that family summable, and a family that
does not converge has no additivity to offer over a cut of the ordinate range. The finiteness of
the ordinates below a fixed height inside the closed rectangle is therefore a leaf of its own.
Second, the band `(1, 3 / 2]` is cut at five quarters, and each half is charged a quarter of the
mean weight integral together with half of the value at height one term. The mean weight
`log (q * t / (2 * pi))` changes sign, so a window charged a share of that integral alone would
have a budget that can be negative while its left hand side is not; splitting the value at height
one term as well keeps every budget nonnegative, and the two quarters of the integral plus the
two halves of the value at height one add up exactly to the right hand side of the statement
being split. Each half carries part of the band's ordinates while being set against half of the
integral, which is what makes both window leaves strictly easier than the statement being split.

The assembly is exactly three ingredients: the identity of sums over the two halves, which is
where the convergence leaf is spent, and the addition of the two window bounds. It has no sorry
of its own. All four leaves are OPEN.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 4, the convergence of the band family. The nonnegative family of the Gaussian
Mellin norms at the zeros in the strip below height `T` is summable. Below a fixed height the
ordinates lie in a compact rectangle and the zeros are isolated there, so only finitely many of
them carry weight; this is the input the window identity below needs, and it is stated on its
own because a sum of the norms over a family that does not converge has no additivity to offer
over a cut of the ordinate range. -/
theorem positive_mass_window_one_norm_summable (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) := by
  sorry

/-- LEAF 2 of 4, the window decomposition. Given the convergence of the band family, the sum
over the ordinates above one and at most three halves is the sum over the ordinates above one
and at most five quarters, plus the sum over the ordinates above five quarters and at most three
halves. As a statement this is the additivity of the zero sum over a disjoint cut of the band,
and it is the only place where the convergence leaf is spent. -/
theorem positive_mass_window_one_window_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖)) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)) := by
  sorry

/-- LEAF 3 of 4, the lower half of the band. The multiplicity weighted sum of the Gaussian
Mellin norms over the zeros whose ordinate lies above one and at most five quarters is at most
one quarter of the mean weight integral over the height interval, plus half of the value at
height one against the shifted log weight at one. This half carries the smallest ordinates of the
positive range, so it is charged the same quarter of the mean weight integral as the other half
and the same half of the value at height one, which keeps its budget nonnegative at the heights
where the mean weight itself is negative. -/
theorem positive_mass_window_one_low_half_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) +
      (1 / 2) * (‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389)) := by
  sorry

/-- LEAF 4 of 4, the upper half of the band. The multiplicity weighted sum of the Gaussian
Mellin norms over the zeros whose ordinate lies above five quarters and at most three halves is
at most one quarter of the mean weight integral over the height interval, plus the other half of
the value at height one against the shifted log weight at one. This half has the same length as
the lower one and is charged the same share, so the two halves together spend only the one half
of the mean weight integral and the whole of the value at height one of the statement being
split. -/
theorem positive_mass_window_one_high_half_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) +
      (1 / 2) * (‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389)) := by
  sorry

/-- The two halves add up to the bound of `positive_mass_window_one_le`. The band `(1, 3 / 2]`
cuts at five quarters into two disjoint halves, the convergence leaf makes that cut an identity
of sums, the two quarters of the mean weight integral add up to the one half of the statement
being split, and the two halves of the value at height one add up to that whole term, so the two
right hand sides add up to the right hand side of the statement being split. -/
theorem positive_mass_window_one_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) := by
  have hs := positive_mass_window_one_norm_summable q χ δ T hT
  refine (le_of_eq (positive_mass_window_one_window_split q χ δ T hT hs)).trans ?_
  refine (add_le_add
    (positive_mass_window_one_low_half_le q χ δ T hT)
    (positive_mass_window_one_high_half_le q χ δ T hT)).trans (le_of_eq ?_)
  ring

end LeanLab.HelfgottMajor.Decomp431a
