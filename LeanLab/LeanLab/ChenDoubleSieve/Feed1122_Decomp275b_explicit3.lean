import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_explicit3_low
import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_explicit3_high

/-!
The elementary F3 value of Wu 2004, arXiv 0705.1652, page 39 equation 10.4 and the page 42
final display: the statement of leaf_explicit3, assembled from the piece on 327/125 to 3,
exactly 8 log 423/327, and the certified bound on the piece on 3 to 5.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ChenDoubleSieve.Feed1122Explicit3
open MeasureTheory intervalIntegral

/-- Wu 2004 page 42 final display, F3 at most 17.327241, with F made explicit. -/
theorem explicit3 :
    4 * (∫ t in (327/125 : ℝ)..5,
      (2 + 2 * ∫ s in (3:ℝ)..max t 3, Real.log (s - 2) / (s - 1)) / t / (1 - t / 6))
      ≤ (17.327241 : ℝ) := by
  set g : ℝ → ℝ := fun t =>
    (2 + 2 * ∫ s in (3:ℝ)..max t 3, Real.log (s - 2) / (s - 1)) / t / (1 - t / 6) with hg
  have hlow := Feed1122Explicit3Low.leaf3_low_le
  have hhigh := Feed1122Explicit3High.high_le
  by_cases hint : IntervalIntegrable g volume (327/125 : ℝ) 5
  · have s1 : Set.uIcc (327/125 : ℝ) 3 ⊆ Set.uIcc (327/125 : ℝ) 5 := by
      rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
      exact Set.Icc_subset_Icc le_rfl (by norm_num)
    have s2 : Set.uIcc (3 : ℝ) 5 ⊆ Set.uIcc (327/125 : ℝ) 5 := by
      rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
      exact Set.Icc_subset_Icc (by norm_num) le_rfl
    have h1 : IntervalIntegrable g volume (327/125 : ℝ) 3 := hint.mono_set s1
    have h2 : IntervalIntegrable g volume (3 : ℝ) 5 := hint.mono_set s2
    rw [← integral_add_adjacent_intervals h1 h2]
    linarith
  · rw [intervalIntegral.integral_undef hint]
    norm_num
end LeanLab.ChenDoubleSieve.Feed1122Explicit3
