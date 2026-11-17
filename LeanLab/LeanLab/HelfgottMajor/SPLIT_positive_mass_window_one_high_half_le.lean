import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_le

/-!
Split of `positive_mass_window_one_high_half_le` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_le` into five leaves.

The statement being split bounds the multiplicity weighted sum of the Gaussian Mellin norms
attached to the positive zeros of a Dirichlet `L`-function in the strip `0 < re < 1` and below
height `T`, restricted to the ordinate band above five quarters and at most three halves, by a
quarter of the critical line norm integral against the mean log weight on `[1, T]`.

The split separates four things the bound needs. First, the band family has to converge at all:
the statement is a sum over every zero in the strip below height `T` and carries no hypothesis on
the zeros, so nothing in the closure makes that family summable, and a family that does not
converge has no additivity to offer over a cut of the band. Second, the band is cut at seven
fifths into two sub-bands of equal length, each charged half the budget; a zero sitting exactly on
the cut belongs to the lower sub-band and is counted once. Third, each sub-band is estimated
against the *positive part* of the mean log weight, one eighth of the integral each, which is what
keeps the two estimates meaningful where the log weight changes sign. Fourth, the transfer from
that positive part back to the signed weight, which is the only place where the sign of
`log (q * t / (2 * pi))` on `[1, T]` is used.

That transfer is where this cut of the statement is loose: the positive part dominates the signed
weight pointwise, so the inequality of the fifth leaf is a claim about the two integrals being
equal in the direction that the argument needs, and it fails as soon as the log weight is negative
somewhere on `[1, T]`, which for `q <= 6` happens for every height. The first four leaves are
sound; the fifth is the defect of the statement being split, isolated on its own.

The assembly is exactly three ingredients: the identity of sums over the two sub-bands, which is
where the convergence leaf is spent, the addition of the two sub-band estimates, and the transfer
leaf. It has no sorry of its own.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 5, the convergence of the band family. The nonnegative family of the Gaussian
Mellin norms at the zeros in the strip below height `T` is summable. Below a fixed height the
ordinates lie in a compact rectangle and the zeros there are isolated, so only finitely many of
them carry weight; this is the input the sub-band identity below needs, and it is stated on its
own because a sum of the norms over a family that does not converge has no additivity to offer
over a cut of the ordinate range. -/
theorem high_half_norm_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) := by
  classical
  exact ZeroCount1623.summable_zeroIdx χ T _

/-- LEAF 2 of 5, the sub-band identity. Given the convergence of the band family, the sum over the
ordinates above five quarters and at most three halves is the sum over the ordinates above five
quarters and at most seven fifths, plus the sum over the ordinates above seven fifths and at most
three halves. As a statement this is the additivity of the zero sum over a disjoint cut of the
band, and it is the only place where the convergence leaf is spent. -/
theorem high_half_window_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖)) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 7 / 5}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 7 / 5 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)) := by
  have hkey : ∀ (x v : ℝ), (if (5 / 4 : ℝ) < x ∧ x ≤ 3 / 2 then v else 0) =
      (if (5 / 4 : ℝ) < x ∧ x ≤ 7 / 5 then v else 0) +
        (if (7 / 5 : ℝ) < x ∧ x ≤ 3 / 2 then v else 0) := by
    intro x v
    by_cases h1 : (5 / 4 : ℝ) < x
    · by_cases h2 : x ≤ 3 / 2
      · by_cases h3 : x ≤ 7 / 5
        · rw [if_pos ⟨h1, h2⟩, if_pos ⟨h1, h3⟩,
            if_neg (by intro h; linarith [h.1, h3])]
          ring
        · rw [if_pos ⟨h1, h2⟩, if_neg (by intro h; linarith [h.2, h3]),
            if_pos ⟨lt_of_not_ge h3, h2⟩]
          ring
      · rw [if_neg (by intro h; linarith [h.2, h2]),
            if_neg (by intro h; linarith [h.2, h2]),
            if_neg (by intro h; linarith [h.2, h2])]
        ring
    · rw [if_neg (by intro h; linarith [h.1, h1]),
          if_neg (by intro h; linarith [h.1, h1]),
          if_neg (by intro h; linarith [h.1, h1])]
      ring
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ =
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 7 / 5}
            (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ +
          Set.indicator {ρ | 7 / 5 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
            (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ := by
    intro ρ
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      hkey ρ.val.im ‖mellinMassTerm χ δ ρ.val‖
  refine (tsum_congr hpt).trans ?_
  exact Summable.tsum_add (hs.indicator _) (hs.indicator _)

/-- LEAF 3 of 5, the lower sub-band against the nonnegative weight. The multiplicity weighted sum
of the Gaussian Mellin norms over the zeros whose ordinate lies above five quarters and at most
seven fifths is at most one eighth of the mean weight integral, where the weight is the positive
part of the log weight. This sub-band carries the smaller ordinates of the band and pays the half
of the budget that has to absorb them. -/
theorem high_half_low_part_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 7 / 5}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          max (log ((q : ℝ) * t / (2 * π))) 0)) := by
  sorry

/-- LEAF 4 of 5, the upper sub-band against the nonnegative weight. The multiplicity weighted sum
of the Gaussian Mellin norms over the zeros whose ordinate lies above seven fifths and at most
three halves is at most one eighth of the mean weight integral against the positive part of the log
weight. This sub-band has the same length as the lower one, carries no endpoint term, and is
charged the same eighth of the budget. -/
theorem high_half_high_part_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 7 / 5 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          max (log ((q : ℝ) * t / (2 * π))) 0)) := by
  sorry

/-- LEAF 5 of 5, the transfer from the positive part of the log weight back to the signed log
weight. A quarter of the mean weight integral against the positive part is at most the same
quarter against the signed log weight. This is the step that replaces the weight by itself, and it
is where the sign of `log (q * t / (2 * pi))` on the height interval is used: the positive part
dominates the signed weight, so the inequality is an equality claim on the integrals and holds only
where the log weight has no negative part on `[1, T]`. -/
theorem high_half_weight_pos_part_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          max (log ((q : ℝ) * t / (2 * π))) 0)) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  sorry

/-- The two sub-bands add up to the bound of `positive_mass_window_one_high_half_le`. The band
`(5 / 4, 3 / 2]` cuts at seven fifths into two disjoint sub-bands, the convergence leaf makes that
cut an identity of sums, the two shares of one eighth each add up to one quarter, and the transfer
leaf replaces the positive part of the weight by the signed log weight. -/
theorem positive_mass_window_one_high_half_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  have hs := high_half_norm_summable q χ δ T hT
  have hsplit := high_half_window_split q χ δ T hT hs
  have hcalc :
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) +
        (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) =
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) := by
    ring
  calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)
      = ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 7 / 5}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 7 / 5 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)) := hsplit
    _ ≤ (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) +
        (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) :=
      add_le_add (high_half_low_part_le q χ δ T hT) (high_half_high_part_le q χ δ T hT)
    _ = (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) := hcalc
    _ ≤ (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            log ((q : ℝ) * t / (2 * π)))) := high_half_weight_pos_part_le q χ δ T hT

end LeanLab.HelfgottMajor.Decomp431a
