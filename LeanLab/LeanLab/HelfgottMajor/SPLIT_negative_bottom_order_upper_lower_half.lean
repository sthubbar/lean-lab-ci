import LeanLab.HelfgottMajor.SPLIT_negative_bottom_order_upper_window

/-!
Split of `negative_bottom_order_upper_lower_half` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_order_upper_window` into four leaves.

The sealed statement bounds the multiplicity sum of the zeros of the short ordinate window
between minus five quarters and minus nine eighths by one eighth of the small height budget
`0.15 * log q + 3.389`.

The split cuts that window of height one eighth into four quarters of height one thirtysecond, at
the heights minus thirtynine thirtyseconds, minus nineteen sixteenths and minus thirtyseven
thirtyseconds, and gives each quarter one thirtysecond of the budget. The four thirtysecond parts
add up to the eighth the sealed statement allows:

`(0.15 * log q + 3.389) / 32 + ... + (0.15 * log q + 3.389) / 32 = (0.15 * log q + 3.389) / 8`.

The four leaves are the four counts. The two quarters next to each other are first combined into
two half counts of height one sixteenth,
`negative_bottom_order_lower_half_low_quarter` and
`negative_bottom_order_lower_half_high_quarter`, and the exhaustion of the window by its two
halves is an inequality between indicator sums proved inside
`negative_bottom_order_upper_lower_half_split`. Neither the two combination theorems nor the
assembly has a sorry of its own. All four leaves are OPEN.

Each leaf bounds a strictly smaller sum than the sealed statement: one quarter of its ordinate
range at one quarter of its budget, a range of height one thirtysecond rather than one eighth.
The split is a partition of the range, not a decomposition of the counting argument, and it is
faithful: the gap between the count of a range and its budget scales with the counted range, so a
leaf falls short of its budget exactly where the sealed statement falls short of its own. The
route that this window belongs to is recorded in the folder as off route and as the wrapper of a
count error rather than a window count, so no leaf here is stronger than the step it comes from;
the split neither adds nor removes that gap.

The window is empty when the height bound is below nine eighths, so every leaf holds at zero
height and at every height below that, and every right hand side is positive because `log q ≥ 0`
for a nonzero conductor, so no leaf is vacuous.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 4. The first quarter of the sealed window. The multiplicity sum of the zeros of
the window from minus five quarters to minus thirtynine thirtyseconds is at most one
thirtysecond of the small height budget. A range of height one thirtysecond; a zero with
multiplicity contributes its multiplicity, and no weight, no character value and no energy
enters. Closed at the bottom end and open at the top, so the four quarters do not overlap. -/
theorem negative_bottom_order_lower_half_first_quarter (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(39 / 32)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 32 := by
  sorry
/-- LEAF 2 of 4. The second quarter of the sealed window. The multiplicity sum of the zeros of
the window from minus thirtynine thirtyseconds to minus nineteen sixteenths is at most one
thirtysecond of the small height budget. Same count over a range of height one thirtysecond,
with the lower end closed and the upper end open. -/
theorem negative_bottom_order_lower_half_second_quarter (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(39 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 32 := by
  sorry
/-- LEAF 3 of 4. The third quarter of the sealed window. The multiplicity sum of the zeros of
the window from minus nineteen sixteenths to minus thirtyseven thirtyseconds is at most one
thirtysecond of the small height budget. Same count over a range of height one thirtysecond,
with the lower end closed and the upper end open. -/
theorem negative_bottom_order_lower_half_third_quarter (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(37 / 32)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 32 := by
  sorry
/-- LEAF 4 of 4. The fourth quarter of the sealed window. The multiplicity sum of the zeros of
the window from minus thirtyseven thirtyseconds to minus nine eighths is at most one
thirtysecond of the small height budget. Same count over a range of height one thirtysecond,
with the lower end closed and the upper end open at the top of the sealed window. -/
theorem negative_bottom_order_lower_half_fourth_quarter (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(37 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 32 := by
  sorry
/-- The two first quarters combined into one half of the sealed window. The window from minus
five quarters to minus nineteen sixteenths is exhausted by its first and second quarter, each of
which is within a thirtysecond of the budget, so its multiplicity sum is within a sixteenth. This
is the intermediate step of the assembly and it has no sorry of its own. -/
theorem negative_bottom_order_lower_half_low_quarter (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 16 := by
  have hlow := negative_bottom_order_lower_half_first_quarter q χ T
  have hhigh := negative_bottom_order_lower_half_second_quarter q χ T
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ ≤
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(39 / 32)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
          Set.indicator {ρ | -(39 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ := by
    intro ρ
    have h1 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)} ↔
        (-(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)) := Iff.rfl
    have h2 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(39 / 32)} ↔
        (-(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(39 / 32)) := Iff.rfl
    have h3 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(39 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)} ↔
        (-(39 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)) := Iff.rfl
    by_cases hw : -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)
    · rw [Set.indicator_of_mem (h1.mpr hw)]
      by_cases hc : ρ.val.im < -(39 / 32)
      · rw [Set.indicator_of_mem (h2.mpr ⟨hw.1, hc⟩),
          Set.indicator_of_notMem (fun h => absurd (h3.mp h).1 (not_le.mpr hc))]
        simp
      · rw [Set.indicator_of_notMem (fun h => absurd (h2.mp h).2 (not_lt.mpr (le_of_not_gt hc))),
          Set.indicator_of_mem (h3.mpr ⟨le_of_not_gt hc, hw.2⟩)]
        simp
    · rw [Set.indicator_of_notMem (fun h => hw (h1.mp h)),
        Set.indicator_of_notMem (fun h => hw ⟨(h2.mp h).1, lt_trans (h2.mp h).2 (by norm_num : -(39 / 32 : ℝ) < -(19 / 16))⟩),
        Set.indicator_of_notMem (fun h => hw
          ⟨le_trans (by norm_num : -(5 / 4 : ℝ) ≤ -(39 / 32)) (h3.mp h).1, (h3.mp h).2⟩)]
      simp
  have hsum : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(39 / 32)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | -(39 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := by
    have hs1 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    have hs2 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(39 / 32)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    have hs3 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(39 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)
        ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            (Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(39 / 32)}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
              Set.indicator {ρ | -(39 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)) :=
          Summable.tsum_le_tsum hpt hs1 (hs2.add hs3)
      _ = _ := Summable.tsum_add hs2 hs3
  linarith [hsum, hlow, hhigh]
/-- The two last quarters combined into one half of the sealed window. The window from minus
nineteen sixteenths to minus nine eighths is exhausted by its third and fourth quarter, each of
which is within a thirtysecond of the budget, so its multiplicity sum is within a sixteenth. This
is the intermediate step of the assembly and it has no sorry of its own. -/
theorem negative_bottom_order_lower_half_high_quarter (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 16 := by
  have hlow := negative_bottom_order_lower_half_third_quarter q χ T
  have hhigh := negative_bottom_order_lower_half_fourth_quarter q χ T
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ ≤
        Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(37 / 32)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
          Set.indicator {ρ | -(37 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ := by
    intro ρ
    have h1 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)} ↔
        (-(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)) := Iff.rfl
    have h2 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(37 / 32)} ↔
        (-(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(37 / 32)) := Iff.rfl
    have h3 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(37 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)} ↔
        (-(37 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)) := Iff.rfl
    by_cases hw : -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)
    · rw [Set.indicator_of_mem (h1.mpr hw)]
      by_cases hc : ρ.val.im < -(37 / 32)
      · rw [Set.indicator_of_mem (h2.mpr ⟨hw.1, hc⟩),
          Set.indicator_of_notMem (fun h => absurd (h3.mp h).1 (not_le.mpr hc))]
        simp
      · rw [Set.indicator_of_notMem (fun h => absurd (h2.mp h).2 (not_lt.mpr (le_of_not_gt hc))),
          Set.indicator_of_mem (h3.mpr ⟨le_of_not_gt hc, hw.2⟩)]
        simp
    · rw [Set.indicator_of_notMem (fun h => hw (h1.mp h)),
        Set.indicator_of_notMem (fun h => hw ⟨(h2.mp h).1, lt_trans (h2.mp h).2 (by norm_num : -(37 / 32 : ℝ) < -(9 / 8))⟩),
        Set.indicator_of_notMem (fun h => hw
          ⟨le_trans (by norm_num : -(19 / 16 : ℝ) ≤ -(37 / 32)) (h3.mp h).1, (h3.mp h).2⟩)]
      simp
  have hsum : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(37 / 32)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | -(37 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := by
    have hs1 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    have hs2 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(37 / 32)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    have hs3 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(37 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)
        ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            (Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(37 / 32)}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
              Set.indicator {ρ | -(37 / 32) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)) :=
          Summable.tsum_le_tsum hpt hs1 (hs2.add hs3)
      _ = _ := Summable.tsum_add hs2 hs3
  linarith [hsum, hlow, hhigh]
/-- The sealed statement of `negative_bottom_order_upper_lower_half`, assembled from the four
leaves through the two combined halves. The window between minus five quarters and minus nine
eighths is exhausted by its two halves, so its indicator sum is at most the sum of the two half
sums; each half is within a sixteenth of the budget; the arithmetic of two sixteenths is exact. -/
theorem negative_bottom_order_upper_lower_half_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 8 := by
  have hlow := negative_bottom_order_lower_half_low_quarter q χ T
  have hhigh := negative_bottom_order_lower_half_high_quarter q χ T
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ ≤
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
          Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ := by
    intro ρ
    have h1 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)} ↔
        (-(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)) := Iff.rfl
    have h2 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)} ↔
        (-(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)) := Iff.rfl
    have h3 : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)} ↔
        (-(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)) := Iff.rfl
    by_cases hw : -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)
    · rw [Set.indicator_of_mem (h1.mpr hw)]
      by_cases hc : ρ.val.im < -(19 / 16)
      · rw [Set.indicator_of_mem (h2.mpr ⟨hw.1, hc⟩),
          Set.indicator_of_notMem (fun h => absurd (h3.mp h).1 (not_le.mpr hc))]
        simp
      · rw [Set.indicator_of_notMem (fun h => absurd (h2.mp h).2 (not_lt.mpr (le_of_not_gt hc))),
          Set.indicator_of_mem (h3.mpr ⟨le_of_not_gt hc, hw.2⟩)]
        simp
    · rw [Set.indicator_of_notMem (fun h => hw (h1.mp h)),
        Set.indicator_of_notMem (fun h => hw ⟨(h2.mp h).1, lt_trans (h2.mp h).2 (by norm_num : -(19 / 16 : ℝ) < -(9 / 8))⟩),
        Set.indicator_of_notMem (fun h => hw
          ⟨le_trans (by norm_num : -(5 / 4 : ℝ) ≤ -(19 / 16)) (h3.mp h).1, (h3.mp h).2⟩)]
      simp
  have hsum : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := by
    have hs1 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    have hs2 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    have hs3 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
      ZeroCount1623.summable_zeroIdx χ T _
    calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)
        ≤ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            (Set.indicator {ρ | -(5 / 4) ≤ ρ.val.im ∧ ρ.val.im < -(19 / 16)}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
              Set.indicator {ρ | -(19 / 16) ≤ ρ.val.im ∧ ρ.val.im < -(9 / 8)}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)) :=
          Summable.tsum_le_tsum hpt hs1 (hs2.add hs3)
      _ = _ := Summable.tsum_add hs2 hs3
  linarith [hsum, hlow, hhigh]

end LeanLab.HelfgottMajor.Decomp431a
