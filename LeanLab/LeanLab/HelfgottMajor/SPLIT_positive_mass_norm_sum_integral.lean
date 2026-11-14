import LeanLab.HelfgottMajor.SPLIT_positive_sampling_raw

/-!
Split of `positive_mass_norm_sum_integral` in
`LeanLab.HelfgottMajor.SPLIT_positive_sampling_raw` into four leaves.

The statement being split bounds the nonnegative, multiplicity weighted sum of the Gaussian
Mellin norms attached to the positive zeros of a primitive Dirichlet `L`-function in the strip
`0 < re < 1` and below height `T`, by three explicit quantities: the critical line norms against
the mean weight divided by `2 * pi` on the height interval `[1, T]`, the derivative norms against
the shifted log weight on the same interval, and the value at height one against the shifted log
weight at one.

The split cuts the height range of the zero set at three points, one and a half, two and four,
and charges each of the four windows to a share of the three budgets. The two windows below
height two share the mean weight integral in two equal parts, the two windows above height two
share the shifted log weight integral in two equal parts, and the value at height one is charged
to the lowest of the four windows. Each window therefore carries a proper piece of the zero sum
against a budget of the size of the whole statement, which is what makes every leaf strictly
easier than the statement being split.

The assembly is exactly three ingredients: the pointwise decomposition of the indicator of the
positive height range into the four windows, the additivity of a summable family over that
disjoint decomposition, and the addition of the four leaf inequalities. It has no sorry of its
own. All four leaves are OPEN.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 4, the lowest window. The multiplicity weighted sum of the Gaussian Mellin norms
over the zeros whose ordinate lies above one and at most three halves is at most half of the mean
weight integral over the height interval, plus the whole value at height one against the shifted
log weight at one. This window holds the smallest ordinates, so it is the one that pays the
height one value; it is charged only half of the mean weight integral because a bounded stretch
of heights carries only boundedly many ordinates. -/
theorem positive_mass_window_one_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) := by
  -- OUT OF REACH 2026-11-14 FREE-ms-leanstral task477:
  -- positive_mass_window_one_le: requires hzeros to bound mellinMassTerm sums by integrals.
  -- Without zero location, no known bound for arbitrary Dirichlet L-function zeros.

/-- LEAF 2 of 4, the second window. The multiplicity weighted sum of the Gaussian Mellin norms
over the zeros whose ordinate lies above three halves and at most two is at most the other half
of the mean weight integral over the height interval. This window is still bounded in height, so
its ordinates are few, and the mean weight alone pays for them. -/
theorem positive_mass_window_two_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  sorry

/-- LEAF 3 of 4, the third window. The multiplicity weighted sum of the Gaussian Mellin norms
over the zeros whose ordinate lies above two and at most four is at most half of the shifted log
weight integral over the height interval. From height two on the derivative carries the weight and
the mean weight integral is no longer spent, so this piece is charged to half of the shifted log
weight budget. -/
theorem positive_mass_window_three_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 2) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  sorry

/-- LEAF 4 of 4, the tail. The multiplicity weighted sum of the Gaussian Mellin norms over the
zeros whose ordinate exceeds four is at most the other half of the shifted log weight integral
over the height interval. This is the piece that carries all but finitely many ordinates, so it
takes the remaining share of the only budget that grows with the height. -/
theorem positive_mass_window_tail_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 4 < ρ.val.im}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 2) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  sorry

/-- The four leaves add up to the bound of `positive_mass_norm_sum_integral`. The positive height
range splits at one and a half, two and four into four disjoint windows, the two shares of the
mean weight integral and the two shares of the shifted log weight integral are each one half
plus one half, and the height one value is carried by the lowest window, so the four right hand
sides add up to the right hand side of the statement being split. -/
theorem positive_mass_norm_sum_integral_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) := by
  classical
  have hsum : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) := by
    apply (Zeros269.low_zero_terms_summable χ δ 1 T hzeros).norm.congr
    intro ρ
    simp [zeroTerm, mellinMassTerm, nsmul_eq_mul]
  have hn : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) :=
    hsum.congr (fun ρ => by
      rw [Real.norm_of_nonneg]
      unfold mellinMassTerm
      positivity)
  have hs1 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := hn.indicator _
  have hs2 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := hn.indicator _
  have hs3 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := hn.indicator _
  have hs4 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | 4 < ρ.val.im}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := hn.indicator _
  have hkey : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ =
        ((Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
              (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ +
            Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2}
              (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) +
          Set.indicator {ρ | 2 < ρ.val.im ∧ ρ.val.im ≤ 4}
              (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) +
        Set.indicator {ρ | 4 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ := by
    intro ρ
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h1 : 1 < ρ.val.im
    · by_cases ha : ρ.val.im ≤ 3 / 2
      · have hb : ¬ (3 / 2 < ρ.val.im) := by linarith
        have hc : ¬ (2 < ρ.val.im) := by linarith
        have hd : ¬ (4 < ρ.val.im) := by linarith
        simp [h1, ha, hb, hc, hd]
      · have ha' : 3 / 2 < ρ.val.im := by linarith
        by_cases hb' : ρ.val.im ≤ 2
        · have hc : ¬ (2 < ρ.val.im) := by linarith
          have hd : ¬ (4 < ρ.val.im) := by linarith
          simp [h1, ha, ha', hb', hc, hd]
        · have hb'' : 2 < ρ.val.im := by linarith
          by_cases hc' : ρ.val.im ≤ 4
          · have hd : ¬ (4 < ρ.val.im) := by linarith
            simp [h1, ha, ha', hb', hb'', hc', hd]
          · have hd' : 4 < ρ.val.im := by linarith
            simp [h1, ha, ha', hb', hb'', hc', hd']
    · have e2 : ¬ (3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2) := fun h => h1 (by linarith [h.1])
      have e3 : ¬ (2 < ρ.val.im ∧ ρ.val.im ≤ 4) := fun h => h1 (by linarith [h.1])
      have e4 : ¬ (4 < ρ.val.im) := by linarith
      simp [h1, e2, e3, e4]
  rw [tsum_congr hkey]
  rw [Summable.tsum_add ((hs1.add hs2).add hs3) hs4,
    Summable.tsum_add (hs1.add hs2) hs3,
    Summable.tsum_add hs1 hs2]
  exact (add_le_add (add_le_add (add_le_add
    (positive_mass_window_one_le q χ δ T hT)
    (positive_mass_window_two_le q χ δ T hT))
    (positive_mass_window_three_le q χ δ T hT))
    (positive_mass_window_tail_le q χ δ T hT)).trans (le_of_eq (by ring))

end LeanLab.HelfgottMajor.Decomp431a
