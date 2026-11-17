module

public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Indicator bookkeeping for the negative lower window on book Part IV pages 433 and 434.
AI wrote this Lean code. Binary Goldbach is open.
-/

public section

namespace LeanLab.HelfgottMajor.Decomp431a

/-- Split a summable real mass at an intermediate ordinate, retaining the common height cutoff. -/
theorem lower_window_mass_partition_of_summable {α : Type*} (height mass : α → ℝ)
    (lower upper radius : ℝ) (hcut : lower ≤ upper) (hmass : Summable mass) :
    (∑' x, Set.indicator {x | height x ≤ upper ∧ |height x| ≤ radius} mass x) =
      (∑' x, Set.indicator {x | height x ≤ lower ∧ |height x| ≤ radius} mass x) +
      (∑' x, Set.indicator
        {x | lower < height x ∧ height x ≤ upper ∧ |height x| ≤ radius} mass x) := by
  classical
  rw [← (hmass.indicator _).tsum_add (hmass.indicator _)]
  apply tsum_congr
  intro x
  by_cases hfar : height x ≤ lower
  · have hwindow : height x ≤ upper := hfar.trans hcut
    have hnear : ¬ lower < height x := not_lt.mpr hfar
    simp [Set.indicator, hfar, hwindow, hnear]
  · have hnear : lower < height x := lt_of_not_ge hfar
    simp [Set.indicator, hfar, hnear]

end LeanLab.HelfgottMajor.Decomp431a

#print axioms LeanLab.HelfgottMajor.Decomp431a.lower_window_mass_partition_of_summable
