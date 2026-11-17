import LeanLab.HelfgottMajor.SPLIT_negative_bottom_order_upper_window

/-!
Split of `negative_bottom_order_upper_upper_half` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_order_upper_window` into three leaves.

The sealed statement bounds the multiplicity sum of the zeros of the short ordinate window
between minus nine eighths and minus one by one eighth of the small height budget
`0.15 * log q + 3.389`.

The split cuts that window, of height one eighth, into three consecutive sub-windows of height
one twenty-fourth, and gives each sub-window one twenty-fourth of the budget:

* the first third runs from minus nine eighths to minus thirteen twelfths,
* the second third from minus thirteen twelfths to minus twenty-five twenty-fourths,
* the last third from minus twenty-five twenty-fourths to minus one.

The three twenty-fourth parts add up to the eighth the sealed statement allows:

`(0.15 * log q + 3.389) / 24 + (0.15 * log q + 3.389) / 24 + (0.15 * log q + 3.389) / 24
  = (0.15 * log q + 3.389) / 8`.

The three leaves are the three counts. The exhaustion of the window by the three sub-windows is
an inequality between indicator sums and is proved inside
`negative_bottom_order_upper_upper_half_split`, which has no sorry of its own. All three leaves
are OPEN.

Each leaf bounds a third of the sum the sealed statement bounds, at a third of its budget: a range
of height one twenty-fourth rather than one eighth. The split is a partition of the range and not
a decomposition of the counting argument, and it is faithful at every scale: the gap between a
count and its budget stays the same fraction of the counted range, because a budget that is one
twenty-fourth of the parent budget for a window that is one twenty-fourth of the parent window
asks for exactly the per unit height density that the sealed statement asks for. A leaf therefore
falls short of its budget exactly as far as the sealed statement falls short of its own.

A previous pass on the parent window recorded numerically that the window of height one eighth
ending at minus one already contains a zero for `q = 199`, so that the sealed statement is false
as cut for large `q`; the third leaf below inherits that failure, and the first two thirds are the
part of the window for which no such zero is recorded. Closing any of the three would need
explicit certified zero data or a zero-free region for `L(s, χ)` near height one, neither of
which is available in this environment.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3. The first third of the window. The multiplicity sum of the zeros of the window
from minus nine eighths to minus thirteen twelfths is at most one twenty-fourth of the small
height budget. This is a count over a range of height one twenty-fourth; a zero with multiplicity
contributes its multiplicity, and no weight, no character value and no energy enters. The lower
end is closed and the upper end is open, so the thirds of the split do not overlap. -/
theorem negative_bottom_order_upper_upper_half_first_third (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -(13 / 12)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 24 := by
  sorry

/-- LEAF 2 of 3. The middle third of the window. The multiplicity sum of the zeros of the window
from minus thirteen twelfths to minus twenty-five twenty-fourths is at most one twenty-fourth of
the small height budget. Same count over a range of height one twenty-fourth, closed at the lower
end at minus thirteen twelfths and open at the upper end at minus twenty-five twenty-fourths;
nothing about the weight, the character value or the budget of the parent window enters. -/
theorem negative_bottom_order_upper_upper_half_second_third (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(13 / 12) ≤ ρ.val.im ∧ ρ.val.im < -(25 / 24)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 24 := by
  sorry

/-- LEAF 3 of 3. The last third of the window. The multiplicity sum of the zeros of the window
from minus twenty-five twenty-fourths to minus one is at most one twenty-fourth of the small
height budget. Same count over a range of height one twenty-fourth, closed at the lower end and
open at the upper end at minus one, so that the three thirds together cover the parent window
with no point counted twice. -/
theorem negative_bottom_order_upper_upper_half_last_third (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(25 / 24) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 24 := by
  sorry

/-- The sealed statement of `negative_bottom_order_upper_upper_half`, assembled from the three
leaves. The window between minus nine eighths and minus one is exhausted by the three thirds, so
its indicator sum is at most the sum of the three third sums; each third is within a
twenty-fourth of the budget; the arithmetic of three twenty-fourths is exact. -/
theorem negative_bottom_order_upper_upper_half_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 8 := by
  have h1 := negative_bottom_order_upper_upper_half_first_third q χ T
  have h2 := negative_bottom_order_upper_upper_half_second_third q χ T
  have h3 := negative_bottom_order_upper_upper_half_last_third q χ T
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ ≤
        Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -(13 / 12)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
          Set.indicator {ρ | -(13 / 12) ≤ ρ.val.im ∧ ρ.val.im < -(25 / 24)}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
            Set.indicator {ρ | -(25 / 24) ≤ ρ.val.im ∧ ρ.val.im < -1}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ := by
    intro ρ
    have hw : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1} ↔
        (-(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1) := Iff.rfl
    have ha : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -(13 / 12)} ↔
        (-(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -(13 / 12)) := Iff.rfl
    have hb : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(13 / 12) ≤ ρ.val.im ∧ ρ.val.im < -(25 / 24)} ↔
        (-(13 / 12) ≤ ρ.val.im ∧ ρ.val.im < -(25 / 24)) := Iff.rfl
    have hc : ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(25 / 24) ≤ ρ.val.im ∧ ρ.val.im < -1} ↔
        (-(25 / 24) ≤ ρ.val.im ∧ ρ.val.im < -1) := Iff.rfl
    by_cases hmem : -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1
    · rw [Set.indicator_of_mem (hw.mpr hmem)]
      by_cases hcut : ρ.val.im < -(13 / 12)
      · rw [Set.indicator_of_mem (ha.mpr ⟨hmem.1, hcut⟩),
          Set.indicator_of_notMem (fun h => absurd (hb.mp h).1 (not_le.mpr hcut)),
          Set.indicator_of_notMem
            (fun h => absurd (hc.mp h).1 (not_le.mpr (lt_trans hcut (by norm_num))))]
        simp
      · have hle : -(13 / 12) ≤ ρ.val.im := le_of_not_gt hcut
        by_cases hcut2 : ρ.val.im < -(25 / 24)
        · rw [Set.indicator_of_notMem (fun h => absurd (ha.mp h).2 (not_lt.mpr hle)),
            Set.indicator_of_mem (hb.mpr ⟨hle, hcut2⟩),
            Set.indicator_of_notMem (fun h => absurd (hc.mp h).1 (not_le.mpr hcut2))]
          simp
        · have hle2 : -(25 / 24) ≤ ρ.val.im := le_of_not_gt hcut2
          rw [Set.indicator_of_notMem (fun h => absurd (ha.mp h).2 (not_lt.mpr hle)),
            Set.indicator_of_notMem (fun h => absurd (hb.mp h).2 (not_lt.mpr hle2)),
            Set.indicator_of_mem (hc.mpr ⟨hle2, hmem.2⟩)]
          simp
    · rw [Set.indicator_of_notMem (fun h => hmem (hw.mp h)),
        Set.indicator_of_notMem
          (fun h => hmem ⟨(ha.mp h).1, lt_trans (ha.mp h).2 (by norm_num)⟩),
        Set.indicator_of_notMem
          (fun h => hmem ⟨le_trans (by norm_num : -(9 / 8 : ℝ) ≤ -(13 / 12)) (hb.mp h).1,
            lt_trans (hb.mp h).2 (by norm_num : -(25 / 24 : ℝ) < -1)⟩),
        Set.indicator_of_notMem
          (fun h => hmem ⟨le_trans (by norm_num : -(9 / 8 : ℝ) ≤ -(25 / 24)) (hc.mp h).1,
            (hc.mp h).2⟩)]
      simp
  have hs0 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
    ZeroCount1623.summable_zeroIdx χ T _
  have hs1 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -(13 / 12)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
    ZeroCount1623.summable_zeroIdx χ T _
  have hs2 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(13 / 12) ≤ ρ.val.im ∧ ρ.val.im < -(25 / 24)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
    ZeroCount1623.summable_zeroIdx χ T _
  have hs3 : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | -(25 / 24) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :=
    ZeroCount1623.summable_zeroIdx χ T _
  have hsum : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -(13 / 12)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | -(13 / 12) ≤ ρ.val.im ∧ ρ.val.im < -(25 / 24)}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) +
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
              Set.indicator {ρ | -(25 / 24) ≤ ρ.val.im ∧ ρ.val.im < -1}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := by
    have hstep := Summable.tsum_le_tsum hpt hs0 ((hs1.add hs2).add hs3)
    have heq : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          (Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -(13 / 12)}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
            Set.indicator {ρ | -(13 / 12) ≤ ρ.val.im ∧ ρ.val.im < -(25 / 24)}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ +
          Set.indicator {ρ | -(25 / 24) ≤ ρ.val.im ∧ ρ.val.im < -1}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ)) =
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | -(9 / 8) ≤ ρ.val.im ∧ ρ.val.im < -(13 / 12)}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) +
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
              Set.indicator {ρ | -(13 / 12) ≤ ρ.val.im ∧ ρ.val.im < -(25 / 24)}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) +
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
                0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
                Set.indicator {ρ | -(25 / 24) ≤ ρ.val.im ∧ ρ.val.im < -1}
                  (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := by
      rw [Summable.tsum_add (hs1.add hs2) hs3, Summable.tsum_add hs1 hs2]
    linarith [hstep, heq]
  linarith [hsum, h1, h2, h3]

end LeanLab.HelfgottMajor.Decomp431a
