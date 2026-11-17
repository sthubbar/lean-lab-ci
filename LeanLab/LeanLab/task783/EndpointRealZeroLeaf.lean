import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Repair of the branch `free-nv-nemosuper/task783`, unit REPAIR/free-nv-nemosuper~task783.

That branch closed the open step `endpoint_real_zero_sum_le` of
`HelfgottMajor.SPLIT_endpoint_strip_sum_le` by way of two smaller statements about the real
zeros of a primitive character below the endpoint height `2 * π / q`, but it wrote the two
`sorry`s into that existing file, which the gate rejects: an existing file may never gain a
sorry.

The two statements are moved here as leaves, and the step the branch was actually proving is
re-proved below from them, sorry free.  The containing file is restored to its state on main,
where the step is still open, so nothing that exists on main changes here.

The leaves ask that the real zeros below the endpoint height, which is at most one on the
range `2 * π ≤ q`, carry at most one unit of multiplicity: once in the shape of a cardinality
bound and once in the shape of a per zero multiplicity bound.  What supplies them is an
explicit verification of the zeros of the primitive characters `L`-functions below height one,
which is not in Mathlib and not in the fifteen module closure of the target file.
-/

namespace LeanLab.task783

open Real

variable {q : ℕ} [NeZero q]

/-- LEAF: the real zeros below the endpoint height number at most one.  On the range
`2 * π ≤ q` the height `2 * π / q` is at most one, and the nontrivial zeros of a primitive
character `L`-function on the real axis below height one are the possible exceptional zero.
This is the bookkeeping half of the piece; it says nothing about multiplicity. -/
theorem endpoint_real_zero_card_le_one (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π ≤ (q : ℝ)) :
    ((LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset.filter
        (fun ρ => ρ.im = 0)).card ≤ 1 := by
  sorry

/-- LEAF: a real zero below the endpoint height is simple, so it carries at most one unit of
multiplicity.  This is the analytic half of the piece: it is what rules out a double real
zero, and like the cardinality bound it needs the zeros below height one to be computed. -/
theorem endpoint_real_zero_mult_le_one (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π ≤ (q : ℝ)) :
    ∀ ρ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset.filter
        (fun ρ => ρ.im = 0), (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- The step the branch closed, assembled from the two leaves.  It is the statement of
`endpoint_real_zero_sum_le` in `HelfgottMajor.SPLIT_endpoint_strip_sum_le`: the multiplicity
weighted count of the real zeros below the endpoint height is at most one.  The assembly is a
bound of a sum of nonnegative terms by the cardinality times the largest term. -/
theorem endpoint_real_zero_sum_le (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π ≤ (q : ℝ)) :
    (∑ ρ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset.filter
        (fun ρ => ρ.im = 0), (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ)) ≤ 1 := by
  have hcard := endpoint_real_zero_card_le_one (q := q) χ hχ hq
  have hmult := endpoint_real_zero_mult_le_one (q := q) χ hχ hq
  calc
    (∑ ρ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset.filter
        (fun ρ => ρ.im = 0), (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ))
        ≤ ((LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ
              (2 * π / q)).toFinset.filter (fun ρ => ρ.im = 0)).card • (1 : ℝ) :=
          Finset.sum_le_card_nsmul _ _ 1 hmult
    _ ≤ 1 := by
      have hc : (((LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ
              (2 * π / q)).toFinset.filter (fun ρ => ρ.im = 0)).card : ℝ) ≤ 1 := by
        exact_mod_cast hcard
      simpa using hc

end LeanLab.task783
