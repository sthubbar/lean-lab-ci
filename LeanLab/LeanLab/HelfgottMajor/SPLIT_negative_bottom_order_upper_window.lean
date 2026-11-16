import LeanLab.HelfgottMajor.SPLIT_negative_bottom_order_sum_le

/-!
Split of `negative_bottom_order_upper_window` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_order_sum_le` into two leaves.

The sealed statement bounds the multiplicity sum of the zeros of the short ordinate window
between minus five quarters and minus one by one quarter of the small height budget
`0.15 * log q + 3.389`.

The split cuts that window at the height minus nine eighths, into a lower half and an upper
half of height one eighth each, and gives each half one eighth of the budget. The two eighth
parts add up to the quarter the sealed statement allows:

`(0.15 * log q + 3.389) / 8 + (0.15 * log q + 3.389) / 8 = (0.15 * log q + 3.389) / 4`.

The two leaves are the two counts. The exhaustion of the window by the two halves is an
inequality between indicator sums and is proved inside
`negative_bottom_order_upper_window_split`, which has no sorry of its own. Both leaves are OPEN.

Each leaf bounds half of the sum the sealed statement bounds, at half of its budget: a range of
height one eighth rather than one quarter. The split is a partition of the range and not a
decomposition of the counting argument, and it is faithful: the gap between a count and its
budget scales with the counted range, so a leaf falls short of its budget exactly where the
sealed statement falls short of its own. The count leaf of the parent
`negative_bottom_order_sum_le` carries the same gap; this split neither adds nor removes it.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 2. The lower half of the window. The multiplicity sum of the zeros of the window
from minus five quarters to minus nine eighths is at most one eighth of the small height
budget. This is a count over a range of height one eighth; a zero with multiplicity contributes
its multiplicity, and no weight, no character value and no energy enters. The lower end is
closed and the upper end is open, so the two halves of the split do not overlap. -/
theorem negative_bottom_order_upper_lower_half (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 8 := by
  sorry

/-- LEAF 2 of 2. The upper half of the window. The multiplicity sum of the zeros of the window
from minus nine eighths to minus one is at most one eighth of the small height budget. Same
count over a range of height one eighth, closed at the lower end at minus nine eighths and open
at the upper end at minus one; nothing about the weight, the character value or the budget of
the parent window enters. -/
theorem negative_bottom_order_upper_upper_half (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 8 := by
  sorry

/-- The sealed statement of `negative_bottom_order_upper_window`, assembled from the two
leaves. The window between minus five quarters and minus one is exhausted by the lower half and
the upper half, so its indicator sum is at most the sum of the two half sums; each half is
within an eighth of the budget; the arithmetic of two eighths is exact. -/
theorem negative_bottom_order_upper_window_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 4 := by
  have hlow := negative_bottom_order_upper_lower_half q χ T
  have hup := negative_bottom_order_upper_upper_half q χ T
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ ≤
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
          Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ := by
    intro ρ
    have h1 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1} ↔
        (-(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1) := Iff.rfl
    have h2 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)} ↔
        (-(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)) := Iff.rfl
    have h3 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1} ↔
        (-(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1) := Iff.rfl
    by_cases hw : -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1
    · rw [Set.indicator_of_mem (h1.mpr hw)]
      by_cases hc : ρ.val.im < -(9 / 8)
      · rw [Set.indicator_of_mem (h2.mpr ⟨hw.1, hc⟩),
          Set.indicator_of_notMem (fun h => absurd (h3.mp h).1 (not_le.mpr hc))]
        simp
      · rw [Set.indicator_of_notMem (fun h => absurd (h2.mp h).2 (not_lt.mpr (le_of_not_gt hc))),
          Set.indicator_of_mem (h3.mpr ⟨le_of_not_gt hc, hw.2⟩)]
        simp
    · rw [Set.indicator_of_notMem (fun h => hw (h1.mp h)),
        Set.indicator_of_notMem (fun h => hw ⟨(h2.mp h).1, lt_trans (h2.mp h).2 (by norm_num)⟩),
        Set.indicator_of_notMem (fun h => hw
          ⟨le_trans (by norm_num : -(5 / 4 : ℝ) ≤ -(9 / 8)) (h3.mp h).1, (h3.mp h).2⟩)]
      simp
  have hsum : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := by
    have hs1 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    have hs2 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    have hs3 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)
        ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            (Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
              Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)) :=
          Summable.tsum_le_tsum hpt hs1 (hs2.add hs3)
      _ = _ := Summable.tsum_add hs2 hs3
  linarith [hsum, hlow, hup]

end LeanLab.HelfgottMajor.Decomp431a
