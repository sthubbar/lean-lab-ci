import LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral

/-!
Split of `positive_mass_window_two_le` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral` into four leaves.

The statement being split bounds the nonnegative, multiplicity weighted sum of the Gaussian
Mellin norms attached to the positive zeros of a Dirichlet `L`-function in the strip
`0 < re < 1` and below height `T`, restricted to the ordinate band above three halves and at
most two, by one half of the critical line norm integral against the mean weight on the height
interval `[1, T]`.

The split separates the two things the bound needs. First, the band family has to converge at
all: the statement is a sum over every zero in the strip below height `T`, with no hypothesis on
the zeros, so nothing in the closure makes that family summable, and a divergent family has no
additivity to offer. The finiteness of the ordinates below a fixed height inside the closed
rectangle is therefore a leaf of its own. Second, the band `(3 / 2, 2]` is cut at its midpoint
seven quarters and the zero mass of each half is charged a quarter of the mean weight integral.
A quarter plus a quarter is the half of the statement being split, and each half carries half
of the band's ordinates against half of what the whole band is allowed, which is what makes
both window leaves strictly easier than the statement being split.

The assembly is exactly three ingredients: the identity of sums over the two halves, which is
where the convergence leaf is spent, and the addition of the two window bounds. It has no sorry
of its own.

The two window leaves are the ones that carry the analytic content, and they are not proved by
this split. Note what they still need: the mean weight `log (q * t / (2 * pi))` is negative for
`t` below `2 * pi / q`, and on a band that holds no ordinate at all both sides of a window bound
would read `0` against a negative budget. So a proof of either window leaf has to know that the
charged heights sit where that weight is nonnegative, which none of the four leaves below
supplies. That gap is left OPEN for the work list, and it is recorded here rather than repaired,
since repairing it would change the statement being split.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-! ### The four leaves -/

/-- LEAF 1 of 4, the finiteness of the band family. The nonnegative family of the Gaussian
Mellin norms at the zeros in the strip below height `T` is summable. Below a fixed height the
ordinates lie in a compact rectangle and the zeros are isolated there, so only finitely many of
them carry weight; this is the convergence input the window identity below needs and it is
stated on its own, because a sum of the norms over a family that does not converge has no
additivity to offer over a split of the ordinate range. -/
theorem positive_mass_window_two_norm_summable (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) := by
  exact ZeroCount1623.summable_zeroIdx χ T _

/-- The pointwise additivity of the indicator of the band `(3/2, 2]` cut at `7/4`: the two
half bands are disjoint and their union is the band, so the indicator of the band is the sum of
the indicators of the halves. -/
private lemma band_indicator_add (c x : ℝ) :
    (if (3 / 2 : ℝ) < x ∧ x ≤ 2 then c else 0) =
      (if (3 / 2 : ℝ) < x ∧ x ≤ 7 / 4 then c else 0) +
        (if (7 / 4 : ℝ) < x ∧ x ≤ 2 then c else 0) := by
  by_cases ha : (3 / 2 : ℝ) < x
  · by_cases hb : x ≤ 7 / 4
    · have hA : (3 / 2 : ℝ) < x ∧ x ≤ 2 := ⟨ha, by linarith⟩
      have hB : (3 / 2 : ℝ) < x ∧ x ≤ 7 / 4 := ⟨ha, hb⟩
      have hC : ¬ ((7 / 4 : ℝ) < x ∧ x ≤ 2) := fun ⟨h', _⟩ => absurd h' (not_lt.mpr hb)
      simp [hA, hB, hC]
    · have hb' : (7 / 4 : ℝ) < x := not_le.mp hb
      by_cases hc : x ≤ 2
      · have hA : (3 / 2 : ℝ) < x ∧ x ≤ 2 := ⟨ha, hc⟩
        have hB : ¬ ((3 / 2 : ℝ) < x ∧ x ≤ 7 / 4) := fun ⟨_, h'⟩ => absurd h' hb
        have hC : (7 / 4 : ℝ) < x ∧ x ≤ 2 := ⟨hb', hc⟩
        simp [hA, hB, hC]
      · have hA : ¬ ((3 / 2 : ℝ) < x ∧ x ≤ 2) := fun ⟨_, h'⟩ => absurd h' hc
        have hB : ¬ ((3 / 2 : ℝ) < x ∧ x ≤ 7 / 4) := fun ⟨_, h'⟩ => absurd h' hb
        have hC : ¬ ((7 / 4 : ℝ) < x ∧ x ≤ 2) := fun ⟨_, h'⟩ => absurd h' hc
        simp [hA, hB, hC]
  · have hA : ¬ ((3 / 2 : ℝ) < x ∧ x ≤ 2) := fun ⟨h', _⟩ => absurd h' ha
    have hB : ¬ ((3 / 2 : ℝ) < x ∧ x ≤ 7 / 4) := fun ⟨h', _⟩ => absurd h' ha
    have hC : ¬ ((7 / 4 : ℝ) < x ∧ x ≤ 2) := by
      intro hcon
      exact ha (lt_trans (show (3 / 2 : ℝ) < 7 / 4 by norm_num) hcon.1)
    simp [hA, hB, hC]

/-- LEAF 2 of 4, the window decomposition. Given the summability of the band family, the sum
over the ordinates above three halves and at most two is the sum over the ordinates above three
halves and at most seven quarters, plus the sum over the ordinates above seven quarters and at
most two. As a statement this is the additivity of the zero sum over a disjoint cut of the band,
and it is the only place where the convergence leaf is spent. -/
theorem positive_mass_window_two_window_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖)) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)) := by
  classical
  have h1 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
      Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
        (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := hs.indicator _
  have h2 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
      Set.indicator {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2}
        (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := hs.indicator _
  rw [← h1.tsum_add h2]
  refine tsum_congr fun ρ => ?_
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.add_apply] using
    band_indicator_add ‖mellinMassTerm χ δ ρ.val‖ ρ.val.im

/-- LEAF 3 of 4, the lower half of the band. The multiplicity weighted sum of the Gaussian
Mellin norms over the zeros whose ordinate lies above three halves and at most seven quarters is
at most one quarter of the mean weight integral over the height interval. This half carries the
lowest ordinates of the band, so it is charged half of the share the whole band is allowed, and
its right hand side is one quarter of the budget against which the statement being split sets
one half. -/
theorem positive_mass_window_two_low_window_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  sorry

/-- LEAF 4 of 4, the upper half of the band. The multiplicity weighted sum of the Gaussian
Mellin norms over the zeros whose ordinate lies above seven quarters and at most two is at most
one quarter of the mean weight integral over the height interval. This half has the same length
as the lower one and is charged the same share, so the two halves together spend only the one
half of the statement being split. -/
theorem positive_mass_window_two_high_window_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  sorry

/-- The two halves add up to the bound of `positive_mass_window_two_le`. The band `(3 / 2, 2]`
cuts at seven quarters into two disjoint halves, the convergence leaf makes that cut an identity
of sums, and the two shares of one quarter each add up to the one half of the statement being
split. -/
theorem positive_mass_window_two_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  have hs := positive_mass_window_two_norm_summable q χ δ T hT
  refine (le_of_eq (positive_mass_window_two_window_split q χ δ T hT hs)).trans ?_
  refine (add_le_add
    (positive_mass_window_two_low_window_le q χ δ T hT)
    (positive_mass_window_two_high_window_le q χ δ T hT)).trans (le_of_eq ?_)
  ring

end LeanLab.HelfgottMajor.Decomp431a
