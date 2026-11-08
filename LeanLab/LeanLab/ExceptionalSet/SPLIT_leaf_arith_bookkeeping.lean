import LeanLab.ExceptionalSet.SPLIT_leaf_decay_rescale

/-!
Split of the scalar bookkeeping step of the rescaling leaf, page 366 of the folder note.

The target `leaf_arith_bookkeeping` compares three scales with no analytic content:

* the factor `B` times the integer half index survives, because `N / 2` as a natural number
  is at most `N` and `e ≤ Y`, so `B * (N / 2) * e ≤ B * N * Y`;
* the hypothesis `1 ≤ N * Y` forces `Y > 0` (as `N` cannot be zero), which is what lets the
  half index be replaced by the full index inside a product;
* the two absolute terms are paid by `2 ≤ 2 * N * Y`, and the remaining `B * N * Y` is
  absorbed by doubling it, giving the constant `2 * B + 2`.

Every leaf below is one scalar inequality; the assembly is a linear combination of them.
No exponential sum, no phase, and no cancellation is involved.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE expSumF)
open LeanLab.ExceptionalSet.Decomp404e (phaseSum)

/-- LEAF. The integer half index, read as a real, is at most the index itself: this is the
only place where the natural-number division `N / 2` enters, and it costs no hypothesis.
At `N = 0` and `N = 1` both sides are `0` and `1`. -/
theorem leaf_half_index_cast_le (N : ℕ) : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
  sorry

/-- LEAF. The hypothesis `1 ≤ N * Y` forces `Y ≥ 0`: `N` cannot be zero in that case, and a
product of the nonnegative `N` with `Y` is at least one, so `Y` itself is positive. -/
theorem leaf_Y_nonneg (N : ℕ) {Y : ℝ} (hNY : 1 ≤ (N : ℝ) * Y) : 0 ≤ Y := by
  sorry

/-- LEAF. The scalar step: multiplying `e ≤ Y` by the nonnegative factor `B * (N / 2)` keeps
the inequality, so the decay input enters only through `Y`. -/
theorem leaf_half_scalar_le (B e Y : ℝ) (N : ℕ) (hB : 0 < B) (he : e ≤ Y) :
    B * ((N / 2 : ℕ) : ℝ) * e ≤ B * ((N / 2 : ℕ) : ℝ) * Y := by
  sorry

/-- LEAF. The half index may be replaced by the full index inside the product: with `B > 0`,
`Y ≥ 0` and the half-index bound, `B * (N / 2) * Y ≤ B * N * Y`. -/
theorem leaf_half_index_product (B Y : ℝ) (N : ℕ) (hB : 0 < B) (hY : 0 ≤ Y)
    (hcast : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ)) :
    B * ((N / 2 : ℕ) : ℝ) * Y ≤ B * (N : ℝ) * Y := by
  sorry

/-- LEAF. The two absolute terms of the target are dominated by twice the product `N * Y`:
`1 ≤ N * Y` gives `2 ≤ 2 * (N * Y)`. -/
theorem leaf_two_le_two_mul (N : ℕ) {Y : ℝ} (hNY : 1 ≤ (N : ℝ) * Y) :
    2 ≤ 2 * ((N : ℝ) * Y) := by
  sorry

/-- LEAF. The surplus that pays for halving the index: `B * N * Y` is nonnegative, hence at
most twice itself, which is the room the constant `2 * B + 2` leaves over `B + 2`. -/
theorem leaf_linear_surplus (B : ℝ) (N : ℕ) (Y : ℝ) (hB : 0 < B)
    (hNY : 1 ≤ (N : ℝ) * Y) :
    B * (N : ℝ) * Y ≤ 2 * B * (N : ℝ) * Y := by
  sorry

/-- The scalar bookkeeping step assembled from the six leaves: multiply the decay input by
`B` and the half index, replace the half index by the full one, and pay the two absolute
terms and the surplus out of `(2 * B + 2) * N * Y`. -/
theorem leaf_arith_bookkeeping_split (B : ℝ) (N : ℕ) (e Y : ℝ) (hB : 0 < B) (he : e ≤ Y)
    (hNY : 1 ≤ (N : ℝ) * Y) :
    B * (N / 2 : ℕ) * e + 2 ≤ (2 * B + 2) * (N : ℝ) * Y := by
  have hY : 0 ≤ Y := leaf_Y_nonneg N hNY
  have hcast : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) := leaf_half_index_cast_le N
  have h1 : B * ((N / 2 : ℕ) : ℝ) * e ≤ B * ((N / 2 : ℕ) : ℝ) * Y :=
    leaf_half_scalar_le B e Y N hB he
  have h2 : B * ((N / 2 : ℕ) : ℝ) * Y ≤ B * (N : ℝ) * Y :=
    leaf_half_index_product B Y N hB hY hcast
  have h3 : 2 ≤ 2 * ((N : ℝ) * Y) := leaf_two_le_two_mul N hNY
  have h4 : B * (N : ℝ) * Y ≤ 2 * B * (N : ℝ) * Y := leaf_linear_surplus B N Y hB hNY
  linarith

end LeanLab.ExceptionalSet.Decomp446c
