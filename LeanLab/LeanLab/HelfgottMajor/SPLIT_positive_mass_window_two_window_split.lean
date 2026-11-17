import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_two_le

/-!
Split of `positive_mass_window_two_window_split` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_window_two_le` into three leaves.

The statement being split is an identity, not an inequality: the multiplicity weighted sum of the
Gaussian Mellin norms over the zeros of the strip below height `T` whose ordinate lies above three
halves and at most two is the sum of the same series over the two halves `(3 / 2, 7 / 4]` and
`(7 / 4, 2]` of that band. Nothing about the sizes of those norms is used, so the identity splits
into exactly the two inputs it needs: the cut of the band at seven quarters is an identity of the
summands at every zero, and each of the two cut series converges, which is what lets the sum of the
summands be split into the sum of the sums.

The convergence is not free. The carrier is the subtype of the zeros of the strip below the fixed
height `T` with no hypothesis on the zeros at all, so the single hypothesis of the statement, the
summability of the norm family, has to be carried into each half; an indicator weighted family is
bounded above by that norm family and nonnegative, so both halves converge.

The assembly spends the three leaves and nothing else: the pointwise identity is turned into an
identity of sums and the sum of the two halves is separated into the sum of the two sums. It has
no sorry of its own.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3, the cut of the band at seven quarters, pointwise at one zero. The indicator of the
band of ordinates above three halves and at most two is, at every zero of the strip below height
`T`, the sum of the indicator of the lower half, above three halves and at most seven quarters, and
the indicator of the upper half, above seven quarters and at most two. The two halves are disjoint
and cover the band, which is the order of the two cuts `3 / 2 < 7 / 4 < 2`. This is the step that
turns the summand of the statement into the summands of the two halves; it is strictly weaker than
the statement because it is one value at a time and carries no sum. -/
theorem positive_mass_window_two_window_pointwise (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}) :
    Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2}
        (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ =
      Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ +
        Set.indicator {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ := by
  by_cases h1 : 3 / 2 < ρ.val.im
  · by_cases h2 : ρ.val.im ≤ 2
    · by_cases h3 : ρ.val.im ≤ 7 / 4
      · rw [Set.indicator_of_mem (show ρ ∈ {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2} from ⟨h1, h2⟩),
            Set.indicator_of_mem (show ρ ∈ {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4} from ⟨h1, h3⟩),
            Set.indicator_of_notMem (show ρ ∉ {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2} from
              fun h => absurd h.1 (not_lt.mpr h3))]
        ring
      · have h34 : 7 / 4 < ρ.val.im := not_le.mp h3
        rw [Set.indicator_of_mem (show ρ ∈ {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2} from ⟨h1, h2⟩),
            Set.indicator_of_notMem (show ρ ∉ {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4} from
              fun h => absurd h.2 (not_le.mpr h34)),
            Set.indicator_of_mem (show ρ ∈ {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2} from ⟨h34, h2⟩)]
        ring
    · have h2' : 2 < ρ.val.im := not_le.mp h2
      have h24 : ¬ (ρ.val.im ≤ 7 / 4) := by linarith
      rw [Set.indicator_of_notMem (show ρ ∉ {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2} from
            fun h => absurd h.2 (not_le.mpr h2')),
          Set.indicator_of_notMem (show ρ ∉ {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4} from
            fun h => absurd h.2 h24),
          Set.indicator_of_notMem (show ρ ∉ {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2} from
            fun h => absurd h.2 (not_le.mpr h2'))]
      ring
  · rw [Set.indicator_of_notMem (show ρ ∉ {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2} from
          fun h => h1 h.1),
        Set.indicator_of_notMem (show ρ ∉ {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4} from
          fun h => h1 h.1),
        Set.indicator_of_notMem (show ρ ∉ {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2} from
          fun h => h1 (by linarith [h.1]))]
    ring

/-- LEAF 2 of 3, the convergence of the lower half. Given the summability of the norm family over
the zeros of the strip below height `T`, the same family weighted by the indicator of the ordinates
above three halves and at most seven quarters is summable. The indicator is zero or the value of a
nonnegative norm and never exceeds it, so the comparison test applies against the summable norm
family; this is the input the separation of the sum of the two halves needs on its first
summand. -/
theorem positive_mass_window_two_window_low_summable (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖)) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := by
  refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) hs
  · by_cases h : ρ ∈ {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
    · rw [Set.indicator_of_mem h]
      exact norm_nonneg _
    · rw [Set.indicator_of_notMem h]
  · by_cases h : ρ ∈ {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      exact norm_nonneg _

/-- LEAF 3 of 3, the convergence of the upper half. Under the same summability hypothesis, the
family weighted by the indicator of the ordinates above seven quarters and at most two is
summable, by the same comparison test. This is the input the separation of the sum of the two
halves needs on its second summand, and together with leaf 2 it is the whole of what convergence
the statement asks for. -/
theorem positive_mass_window_two_window_high_summable (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖)) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) := by
  refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) hs
  · by_cases h : ρ ∈ {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2}
    · rw [Set.indicator_of_mem h]
      exact norm_nonneg _
    · rw [Set.indicator_of_notMem h]
  · by_cases h : ρ ∈ {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2}
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      exact norm_nonneg _

/-- The cut band identity of `positive_mass_window_two_window_split`. The pointwise identity of the
first leaf holds at every zero, so the sums over the zeros agree with the sum of the summands of
the two halves; the two sums of the halves then separate by the convergence of the second and third
leaves. Nothing else is used, and the identity is not assumed. -/
theorem positive_mass_window_two_window_split_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖)) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) = ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) + (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, Set.indicator {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)) := by
  refine (tsum_congr (fun ρ => positive_mass_window_two_window_pointwise q χ δ T ρ)).trans ?_
  exact (positive_mass_window_two_window_low_summable q χ δ T hT hs).tsum_add
    (positive_mass_window_two_window_high_summable q χ δ T hT hs)

end LeanLab.HelfgottMajor.Decomp431a
