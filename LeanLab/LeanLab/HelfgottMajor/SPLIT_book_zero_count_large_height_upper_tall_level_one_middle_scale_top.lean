import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one_middle_scale_low

/-!
# Split of `book_zero_count_large_height_upper_tall_level_one_middle_scale_top`

Subrange `10 ^ 12 ≤ T ≤ 10 ^ 13` at level one, from Corollary 1 of Trudgian 2014, which fits
the book error for every `T ≥ 10 ^ 10`.
The leaves, the bridge from the open count to `bookCount` and the arithmetic are in
`SPLIT_book_zero_count_large_height_upper_tall_level_one_middle_scale_low`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- Split of the subrange `10 ^ 12 ≤ T ≤ 10 ^ 13`, from Corollary 1 of Trudgian 2014. -/
theorem book_zero_count_large_height_upper_tall_level_one_middle_scale_top_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT12 : 10 ^ 12 ≤ T) (hT13 : T ≤ 10 ^ 13)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  subst hq1
  have hT0 : 0 < T := by linarith
  have h10 : (10 : ℝ) ^ 10 ≤ T := le_trans (by norm_num) hT12
  have hlog : 0 < Real.log T := by linarith [le_log_of_ge_1e10 h10]
  refine level_one_upper_of_bound χ hT
    (fun t => 0.112 * Real.log t + 0.278 * Real.log (Real.log t) + 2.510 + 0.2 / t)
    ((((continuousAt_const.mul (Real.continuousAt_log hT0.ne')).add
      (continuousAt_const.mul ((Real.continuousAt_log hT0.ne').log hlog.ne'))).add
        continuousAt_const).add (continuousAt_const.div continuousAt_id hT0.ne')) ?_
    (corollary1_budget h10)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have he : Real.exp 1 ≤ t := by
    have : T < t := ht
    have := Real.exp_one_lt_d9
    norm_num at h10; linarith
  have h := (abs_le.mp (trudgian2014_corollary1 χ he)).2
  linarith

end LeanLab.HelfgottMajor.ZeroCount1623
