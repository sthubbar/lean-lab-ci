import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_two_le

/-!
Split of `positive_mass_window_two_low_window_le` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_window_two_le` into four leaves.

The statement being split bounds the nonnegative, multiplicity weighted sum of the Gaussian
Mellin norms attached to the positive zeros of a Dirichlet `L`-function in the strip
`0 < re < 1` and below height `T`, restricted to the lower half of the middle ordinate band,
above three halves and at most seven quarters, by one quarter of the critical line norm integral
against the mean weight on the height interval `[1, T]`.

The split separates the two things the bound needs. First, the band family has to converge at
all: the statement is a sum over every zero in the strip below height `T`, with no hypothesis on
the zeros, so nothing in the closure makes that family summable, and a family that does not
converge has no additivity to offer over a cut of the ordinate range. The finiteness of the
ordinates below a fixed height inside the closed rectangle is therefore a leaf of its own.
Second, the band `(3 / 2, 7 / 4]` is cut at its midpoint thirteen eighths and the zero mass of
each half is charged one eighth of the mean weight integral. An eighth plus an eighth is the
quarter of the statement being split, and each half carries half of the band's ordinates against
half of what the whole band is allowed, which is what makes both half leaves strictly easier than
the statement being split.

The assembly is exactly three ingredients: the identity of sums over the two halves, which is
where the convergence leaf is spent, and the addition of the two half bounds. It has no sorry of
its own. All four leaves are OPEN, and the two half bounds are the ones that carry the analytic
content.

Note what the half bounds still need, and where the statement as cut is defective. The mean weight
`log (q * t / (2 * pi))` is negative for `t` below `2 * pi / q`, and the statement that this band
descends from carries the hypothesis `2 * pi * exp 2 ≤ (q : ℝ) * T`, which the window statements
dropped. Without it a half bound cannot hold: at `T` small enough that the band holds no ordinate,
the left side is zero because the zero set is empty at that height, while the integrand is
nonnegative and the weight is negative on `[1, T]`, so the right side is negative. On a band that
does hold an ordinate the bound can only hold if the charged heights sit where that weight is
nonnegative. Closing either half therefore needs that hypothesis restored, which is a re-cut of
the window statement, and it is left to the work list, since supplying it here would change the
statement being split.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-! ### The four leaves -/

/-- LEAF 1 of 4, the convergence of the band family. The nonnegative family of the Gaussian
Mellin norms at the zeros in the strip below height `T` is summable. Below a fixed height the
ordinates lie in a compact rectangle and the zeros are isolated there, so only finitely many of
them carry weight; this is the input the window identity below needs, and it is stated on its own
because a sum of the norms over a family that does not converge has no additivity to offer over a
cut of the ordinate range. -/
theorem positive_mass_window_two_low_window_norm_summable (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) := by
  sorry

/-- LEAF 2 of 4, the window decomposition. Given the convergence of the band family, the sum
over the ordinates above three halves and at most seven quarters is the sum over the ordinates
above three halves and at most thirteen eighths, plus the sum over the ordinates above thirteen
eighths and at most seven quarters. As a statement this is the additivity of the zero sum over a
disjoint cut of the band, and it is the only place where the convergence leaf is spent. -/
theorem positive_mass_window_two_low_window_window_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖)) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 13 / 8}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 13 / 8 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)) := by
  sorry

/-- LEAF 3 of 4, the lower half of the band. The multiplicity weighted sum of the Gaussian
Mellin norms over the zeros whose ordinate lies above three halves and at most thirteen eighths
is at most one eighth of the mean weight integral over the height interval. This half carries the
smallest ordinates of the band and only half of its ordinates, so it is charged half of the share
the whole band is allowed, an eighth against the quarter of the statement being split. -/
theorem positive_mass_window_two_low_window_low_half_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 13 / 8}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  sorry

/-- LEAF 4 of 4, the upper half of the band. The multiplicity weighted sum of the Gaussian
Mellin norms over the zeros whose ordinate lies above thirteen eighths and at most seven quarters
is at most one eighth of the mean weight integral over the height interval. This half has the same
length as the lower one and is charged the same eighth, so the two halves together spend only the
quarter of the statement being split. -/
theorem positive_mass_window_two_low_window_high_half_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 13 / 8 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  sorry

/-- The two halves add up to the bound of `positive_mass_window_two_low_window_le`. The band
`(3 / 2, 7 / 4]` cuts at thirteen eighths into two disjoint halves, the convergence leaf makes
that cut an identity of sums, and the two shares of one eighth each add up to the one quarter of
the statement being split. -/
theorem positive_mass_window_two_low_window_le_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  have hs := positive_mass_window_two_low_window_norm_summable q χ δ T hT
  refine (le_of_eq (positive_mass_window_two_low_window_window_split q χ δ T hT hs)).trans ?_
  refine (add_le_add
    (positive_mass_window_two_low_window_low_half_le q χ δ T hT)
    (positive_mass_window_two_low_window_high_half_le q χ δ T hT)).trans (le_of_eq ?_)
  ring

end LeanLab.HelfgottMajor.Decomp431a
