import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one_middle_scale_low

/-!
# Split of `book_zero_count_large_height_upper_tall_level_one_middle_scale_central_low`

Subrange `10 ^ 8 ≤ T ≤ 10 ^ 10` at level one. Up to `5 × 10 ^ 8` the count comes from
display 1.2 of Trudgian 2014, above it from Table 2 row `10 ^ 8`; Corollary 1 alone does not
fit the book error on this subrange.
The leaves, the bridge from the open count to `bookCount` and the arithmetic are in
`SPLIT_book_zero_count_large_height_upper_tall_level_one_middle_scale_low`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- Split of the lower central subrange `10 ^ 8 ≤ T ≤ 10 ^ 10`. -/
theorem book_zero_count_large_height_upper_tall_level_one_middle_scale_central_low_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT8 : 10 ^ 8 ≤ T) (hT10 : T ≤ 10 ^ 10)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  subst hq1
  have hT0 : 0 < T := by linarith
  rcases le_or_gt T 5e8 with h5 | h5
  · refine level_one_upper_of_bound χ hT (fun t => 2.31366 + 0.2 / t)
      (continuousAt_const.add (continuousAt_const.div continuousAt_id hT0.ne')) ?_
      (eq12_budget hT)
    have hmem : Ioo T 5.45e8 ∈ 𝓝[>] T := Ioo_mem_nhdsGT (by norm_num at h5 ⊢; linarith)
    filter_upwards [hmem] with t ht
    have h := (abs_le.mp (trudgian2014_eq12_count χ (hT.trans ht.1.le) ht.2.le)).2
    linarith
  · refine level_one_upper_of_bound χ hT (fun t => 0.234 * Real.log t + 0.2 / t)
      ((continuousAt_const.mul (Real.continuousAt_log hT0.ne')).add
        (continuousAt_const.div continuousAt_id hT0.ne')) ?_ (table2_budget hT hT10)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (10 : ℝ) ^ 8 < t := by
      have : T < t := ht
      norm_num at h5 ⊢; linarith
    have h := (abs_le.mp (trudgian2014_table2_count χ ht')).2
    linarith

end LeanLab.HelfgottMajor.ZeroCount1623
