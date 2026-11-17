import LeanLab.HelfgottMajor.SPLIT_negative_bottom_order_sum_le

/-!
Split of `negative_bottom_order_lower_window` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_order_sum_le` into three leaves.

The sealed statement bounds the multiplicity sum of the zeros of the ordinate window
`-(3 / 2) < im < -(5 / 4)` by one quarter of the small height budget `0.15 * log q + 3.389`,
at every index height `T`.

The split separates the height from the count. The leaf `_mono` says the sum grows with the
index height, so below height `3 / 2` the sum is at most its value at `3 / 2`. The leaf `_sat`
says the window sits inside the band of height `3 / 2`, so above height `3 / 2` the sum is
still at most its value at `3 / 2`. The leaf `_at_max` is the count at exactly height `3 / 2`:
a band of height one quarter, and the only leaf that carries analysis.

Leaves 1 and 2 are proved from `ZeroCount1623.summable_zeroIdx`, which makes the
index set finite; leaf 3 stays OPEN.

The three leaves exhaust the height: `_mono` and `_sat` cover `T ≤ 3 / 2` and `3 / 2 ≤ T`, and
`_at_max` is the common bound. The assembly
`negative_bottom_order_lower_window_split` is that case split and has no sorry of its own; it
does not use `negative_bottom_order_lower_window`.

Degenerate values behave: at `T ≤ 3 / 2` the index set of `_mono` is a subset of the one at
`3 / 2` and the summands are nonnegative multiplicities, at `T ≤ 5 / 4` every summand of both
sides is the indicator at a point outside the window and vanishes, and `q ≥ 1` by `[NeZero q]`
so the budget `(0.15 * log q + 3.389) / 4` is at least `0.84725` and never negative.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: 1 of 3, monotonicity in the index height. Raising the height `T` to `T'` only enlarges
the set of zeros the outer window sum runs over, and a multiplicity is nonnegative, so the sum
at the lower height is at most the sum at the higher one. No budget, no conductor and no
character value enters; this is an inequality between two sums, not the sealed statement. -/
theorem negative_bottom_order_lower_window_mono (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) {T T' : ℝ} (hTT : T ≤ T') :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T'},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := by
  have hbridge : ∀ U : ℝ,
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ U},
          Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) =
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ U},
            Set.indicator {z : ℂ | -(3 / 2) < z.im ∧ z.im < -(5 / 4)}
              (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) ρ.val) := by
    intro U
    refine tsum_congr (fun ρ => ?_)
    by_cases h : -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, h, ite_true]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, h, ite_false]
  have hsub : (ZeroCount1623.stripZeros_finite χ T).toFinset ⊆
      (ZeroCount1623.stripZeros_finite χ T').toFinset := by
    intro ρ hρ
    have hρ' := (ZeroCount1623.stripZeros_finite χ T).mem_toFinset.mp hρ
    exact (ZeroCount1623.stripZeros_finite χ T').mem_toFinset.mpr
      ⟨hρ'.1, hρ'.2.1, hρ'.2.2.1, hρ'.2.2.2.trans hTT⟩
  rw [hbridge T, hbridge T', ZeroCount1623.tsum_zeroIdx χ T,
    ZeroCount1623.tsum_zeroIdx χ T']
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro x _ _
  by_cases hx : -(3 / 2) < x.im ∧ x.im < -(5 / 4)
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ite_true]
    positivity
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ite_false]
    norm_num

/-- LEAF: 2 of 3, saturation above height three halves. A zero of the window carries
`|im| < 3 / 2`, so once the index height reaches `3 / 2` the window adds no index and the sum
at the higher height is still at most the sum at `3 / 2`. Again no budget and no count enters;
this is the containment of the window in the band of height three halves. -/
theorem negative_bottom_order_lower_window_sat (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : (3 / 2) ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (3 / 2)},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) := by
  have hbridge : ∀ U : ℝ,
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ U},
          Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) =
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ U},
            Set.indicator {z : ℂ | -(3 / 2) < z.im ∧ z.im < -(5 / 4)}
              (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) ρ.val) := by
    intro U
    refine tsum_congr (fun ρ => ?_)
    by_cases h : -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, h, ite_true]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, h, ite_false]
  have hsub : (ZeroCount1623.stripZeros_finite χ (3 / 2)).toFinset ⊆
      (ZeroCount1623.stripZeros_finite χ T).toFinset := by
    intro ρ hρ
    have hρ' := (ZeroCount1623.stripZeros_finite χ (3 / 2)).mem_toFinset.mp hρ
    exact (ZeroCount1623.stripZeros_finite χ T).mem_toFinset.mpr
      ⟨hρ'.1, hρ'.2.1, hρ'.2.2.1, hρ'.2.2.2.trans hT⟩
  have hzero : ∀ ρ ∈ (ZeroCount1623.stripZeros_finite χ T).toFinset,
      ρ ∉ (ZeroCount1623.stripZeros_finite χ (3 / 2)).toFinset →
      Set.indicator {z : ℂ | -(3 / 2) < z.im ∧ z.im < -(5 / 4)}
        (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) ρ = 0 := by
    intro ρ hT' hn
    have hρ' := (ZeroCount1623.stripZeros_finite χ T).mem_toFinset.mp hT'
    have hh : ¬ |ρ.im| ≤ (3 / 2) := fun h => hn
      ((ZeroCount1623.stripZeros_finite χ (3 / 2)).mem_toFinset.mpr
        ⟨hρ'.1, hρ'.2.1, hρ'.2.2.1, h⟩)
    have hw : ¬ (-(3 / 2) < ρ.im ∧ ρ.im < -(5 / 4)) := by
      rintro ⟨h1, h2⟩
      exact hh (by rw [abs_le]; constructor <;> linarith)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hw, ite_false]
  rw [hbridge T, hbridge (3 / 2), ZeroCount1623.tsum_zeroIdx χ T,
    ZeroCount1623.tsum_zeroIdx χ (3 / 2)]
  exact le_of_eq (Finset.sum_subset hsub hzero).symm

/-- LEAF: 3 of 3, the count at height three halves. The multiplicity sum of the zeros of the
window from minus three halves to minus five quarters, taken over the band of index height
three halves, is at most one quarter of the small height budget. This is the sealed count at a
single height, a range of height one quarter, and it is what carries the analysis. -/
theorem negative_bottom_order_lower_window_at_max (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (3 / 2)},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 4 := by
  sorry

/-- The sealed statement of `negative_bottom_order_lower_window`, assembled from the three
leaves. Below height three halves monotonicity bounds the sum by its value at three halves and
above that height saturation does the same; the value at three halves is within a quarter of
the budget. The case split is exhaustive without qualification on `T`. -/
theorem negative_bottom_order_lower_window_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -(5 / 4)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) ≤
      (0.15 * log (q : ℝ) + 3.389) / 4 := by
  by_cases hT : T ≤ 3 / 2
  · exact (negative_bottom_order_lower_window_mono q χ hT).trans
      (negative_bottom_order_lower_window_at_max q χ)
  · exact (negative_bottom_order_lower_window_sat q χ (le_of_lt (not_le.mp hT))).trans
      (negative_bottom_order_lower_window_at_max q χ)

end LeanLab.HelfgottMajor.Decomp431a
