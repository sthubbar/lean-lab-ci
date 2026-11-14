import LeanLab.HelfgottMajor.SPLIT_negative_mass_bottom_le

/-!
Split of `negative_bottom_order_sum_le` in `LeanLab.HelfgottMajor.SPLIT_negative_mass_bottom_le`
into two leaves.

The sealed statement bounds twice the multiplicity sum of the zeros of the short ordinate window
between minus three halves and minus one by the small height budget `0.15 * log q + 3.389`.

The split cuts the window at the height minus five quarters, the same cut the weight leaf of the
parent uses. The outer half runs from minus three halves to minus five quarters and the inner
half from minus five quarters to minus one. Each half is a range of height one quarter and each
carries one quarter of the budget, so the two counts add up to exactly the sealed budget:

`2 * ((0.15 * log q + 3.389) / 4 + (0.15 * log q + 3.389) / 4) = 0.15 * log q + 3.389`.

The two leaves are the two counts. The exhaustion of the window by the two halves is an
inequality between indicator sums and is proved inside `negative_bottom_order_sum_le_split`,
which has no sorry of its own. Both leaves are OPEN.

Each leaf bounds a strictly smaller sum than the sealed statement: half the ordinate range at
one quarter of the budget rather than the whole range at the whole budget. The split is a
partition of the range, not a decomposition of the counting argument, and it is faithful: the
gap between the count of a range and the budget grows in proportion to the counted range, so a
leaf falls short exactly where the sealed statement does.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 2. The outer count. The multiplicity sum of the zeros of the window from minus
three halves to minus five quarters is at most one quarter of the small height budget. This is
the count over a range of height one quarter and it produces no weight, no character value and
no energy; a zero with multiplicity contributes its multiplicity. -/
theorem negative_bottom_order_lower_window (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 4 := by
  sorry

/-- LEAF 2 of 2. The inner count. The multiplicity sum of the zeros of the window from minus
five quarters to minus one is at most one quarter of the small height budget. Same count over a
range of height one quarter, closed at the upper end at minus one and at the lower end at minus
five quarters; nothing about the weight or the budget of the parent enters. -/
theorem negative_bottom_order_upper_window (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 4 := by
  sorry

/-- The sealed statement of `negative_bottom_order_sum_le`, assembled from the two leaves. The
window between minus three halves and minus one is exhausted by the outer half and the inner
half, so its indicator sum is at most the sum of the two half sums; each half is within a
quarter of the budget; the arithmetic of four quarters is exact. -/
theorem negative_bottom_order_sum_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) :
    2 * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      0.15 * log (q : ℝ) + 3.389 := by
  have hout := negative_bottom_order_lower_window q χ T
  have hin := negative_bottom_order_upper_window q χ T
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ ≤
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
          Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ := by
    intro ρ
    have h1 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1} ↔
        (-(3 / 2) < ρ.val.im ∧ ρ.val.im < -1) := Iff.rfl
    have h2 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)} ↔
        (-(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)) := Iff.rfl
    have h3 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1} ↔
        (-(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1) := Iff.rfl
    by_cases hw : -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1
    · rw [Set.indicator_of_mem (h1.mpr hw)]
      by_cases hc : ρ.val.im < -(5 / 4)
      · rw [Set.indicator_of_mem (h2.mpr ⟨hw.1, hc⟩),
          Set.indicator_of_notMem (fun h => absurd (h3.mp h).1 (not_le.mpr hc)), add_zero]
      · rw [Set.indicator_of_notMem (fun h => absurd (h2.mp h).2 (not_lt.mpr (le_of_not_gt hc))),
          Set.indicator_of_mem (h3.mpr ⟨le_of_not_gt hc, hw.2⟩), zero_add]
    · rw [Set.indicator_of_notMem (fun h => hw (h1.mp h))]
      rw [Set.indicator_of_notMem (fun h => hw ⟨(h2.mp h).1, lt_trans (h2.mp h).2 (by norm_num)⟩),
        Set.indicator_of_notMem (fun h => hw ⟨lt_of_lt_of_le (by norm_num) (h3.mp h).1, (h3.mp h).2⟩),
        add_zero]
  have hsum : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := by
    have hs1 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    have hs2 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    have hs3 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)
        ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            (Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
              Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -1}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)) :=
          Summable.tsum_le_tsum hpt hs1 (hs2.add hs3)
      _ = _ := Summable.tsum_add hs2 hs3
  linarith [hsum, hout, hin]

end LeanLab.HelfgottMajor.Decomp431a
