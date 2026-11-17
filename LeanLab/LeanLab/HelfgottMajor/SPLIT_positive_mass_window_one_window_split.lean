import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_le

/-!
Split of `positive_mass_window_one_window_split` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_le` into three leaves.

The statement being split is an identity, not an inequality: the multiplicity weighted sum of the
Gaussian Mellin norms over the zeros of the strip below height `T` whose ordinate lies above one
and at most three halves is the sum of the same series over the two halves `(1, 5 / 4]` and
`(5 / 4, 3 / 2]` of that band. Nothing about the sizes of those norms is used, so the identity
splits into exactly the two inputs it needs: the cut of the band into the two disjoint half open
intervals is an identity of the summands at every zero, and each of the two cut series converges,
which is what lets the sum of the summands be split into the sum of the sums.

The convergence is not free. The carrier is the subtype of the zeros of the strip below the fixed
height `T` with no hypothesis on the zeros at all, so the single hypothesis of the statement, the
summability of the norm family, has to be carried into each half; an indicator weighted family is
bounded above by that norm family and nonnegative, so both halves converge.

The assembly spends the three leaves and nothing else: the pointwise identity is turned into an
identity of sums and the sum of the two halves is separated into the sum of the two sums. It has
no sorry of its own. All three leaves are PROVED.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- The real cut `(1, 3 / 2]` at `5 / 4`, at a constant value. -/
private lemma band_indicator_add_window_one (c x : ℝ) :
    (if (1 : ℝ) < x ∧ x ≤ 3 / 2 then c else 0) =
      (if (1 : ℝ) < x ∧ x ≤ 5 / 4 then c else 0) +
        (if (5 / 4 : ℝ) < x ∧ x ≤ 3 / 2 then c else 0) := by
  by_cases hA : (1 : ℝ) < x ∧ x ≤ 3 / 2
  · have ha : (1 : ℝ) < x := hA.1
    have hb : x ≤ 3 / 2 := hA.2
    by_cases h2 : x ≤ 5 / 4
    · have hB : (1 : ℝ) < x ∧ x ≤ 5 / 4 := ⟨ha, h2⟩
      have hC : ¬ ((5 / 4 : ℝ) < x ∧ x ≤ 3 / 2) := fun h => absurd h.1 (not_lt.mpr h2)
      simp [hA, hB, hC]
    · have hB : ¬ ((1 : ℝ) < x ∧ x ≤ 5 / 4) := fun h => absurd h.2 h2
      have hC : (5 / 4 : ℝ) < x ∧ x ≤ 3 / 2 := ⟨by linarith, hb⟩
      simp [hA, hB, hC]
  · have hB : ¬ ((1 : ℝ) < x ∧ x ≤ 5 / 4) := fun h => hA ⟨h.1, by linarith [h.2]⟩
    have hC : ¬ ((5 / 4 : ℝ) < x ∧ x ≤ 3 / 2) := fun h => hA ⟨by linarith [h.1], h.2⟩
    simp [hA, hB, hC]

/-- LEAF 1 of 3, the cut of the band at five quarters, pointwise at one zero. The indicator of the
band of ordinates above one and at most three halves is, at every zero of the strip below height
`T`, the sum of the indicator of the lower half, above one and at most five quarters, and the
indicator of the upper half, above five quarters and at most three halves. The two halves are
disjoint and cover the band, which is the order of the two cuts `1 < 5 / 4 < 3 / 2`. This is the
step that turns the summand of the statement into the summands of the two halves; it is strictly
weaker than the statement because it is one value at a time and carries no sum. -/
theorem positive_mass_window_one_window_pointwise (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}) :
    Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
        (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ =
      Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ +
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ := by
  classical
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.add_apply] using
    band_indicator_add_window_one ‖mellinMassTerm χ δ ρ.val‖ ρ.val.im

/-- LEAF 2 of 3, the convergence of the lower half. Given the summability of the norm family over
the zeros of the strip below height `T`, the same family weighted by the indicator of the
ordinates above one and at most five quarters is summable. The indicator is zero or one and the
norms are nonnegative and summable, so the comparison test applies; this is the input the
separation of the sum of the two halves needs on its first summand. -/
theorem positive_mass_window_one_window_low_summable (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖)) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | 1 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := by
  classical
  exact hs.indicator _

/-- LEAF 3 of 3, the convergence of the upper half. Under the same summability hypothesis, the
family weighted by the indicator of the ordinates above five quarters and at most three halves is
summable, by the same comparison test. This is the input the separation of the sum of the two
halves needs on its second summand, and together with leaf 2 it is the whole of what convergence
the statement asks for. -/
theorem positive_mass_window_one_window_high_summable (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖)) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := by
  classical
  exact hs.indicator _

/-- The cut band identity of `positive_mass_window_one_window_split`. The pointwise identity of the
first leaf holds at every zero, so the sums over the zeros agree with the sum of the summands of
the two halves; the two sums of the halves then separate by the convergence of the second and
third leaves. Nothing else is used, and the bound is not assumed. -/
theorem positive_mass_window_one_window_split_split (q : ℕ) [NeZero q]
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
  refine (tsum_congr (fun ρ => positive_mass_window_one_window_pointwise q χ δ T ρ)).trans ?_
  exact (positive_mass_window_one_window_low_summable q χ δ T hT hs).tsum_add
    (positive_mass_window_one_window_high_summable q χ δ T hT hs)

end LeanLab.HelfgottMajor.Decomp431a
