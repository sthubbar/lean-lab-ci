/-
AI wrote this Lean code. CODEX task94.
P0009 arXiv 2207.09452 v6, Lemma 17, page 17, eqs 49 and 50.
Scalar audit of the error envelope from the displayed theta bound.
The integral of M times 1 plus u over u cubed from L to infinity is
M times 1 over L plus 1 over 2 L squared.
This file verifies the scalar comparisons after that standard substitution.
Lemma17Upper stays cited. The proof step is a QUESTION.
Binary Goldbach is OPEN.
-/
import Mathlib

open Real Set Filter
open scoped Topology
namespace LeanLab.ChenExplicit.Decomp94b

/-- LEAF. P0009 page 17, eq 50, scalar sum of point and tail envelopes. -/
theorem envelope_identity (L : ℝ) (hL : L ≠ 0) :
    5.7410e-13 / L ^ 2 + 5.7410e-13 * (1 / L + 1 / (2 * L ^ 2)) =
      5.7410e-13 / L * (1 + 3 / (2 * L)) := by
  field_simp
  ring

/-- LEAF. P0009 page 17, the displayed theta estimate controls the point term
by the printed eq 49 allowance when L is at least 4000. -/
theorem point_term_le_printed (L : ℝ) (hL : 4000 ≤ L) :
    5.7410e-13 / L ^ 2 ≤ 1.436e-16 / L := by
  have h0 : 0 < L := by linarith
  rw [div_le_div_iff₀ (sq_pos_of_pos h0) h0]
  have hm := mul_nonneg (show 0 ≤ 1.436e-16 * L - 5.7410e-13 by linarith) h0.le
  nlinarith

/-- LEAF. P0009 page 17, eq 50, negative result for the uniform theta envelope.
The full scalar envelope exceeds the printed eq 49 allowance. -/
theorem envelope_gt_printed (L : ℝ) (hL : 4000 ≤ L) :
    1.436e-16 / L <
      5.7410e-13 / L ^ 2 + 5.7410e-13 * (1 / L + 1 / (2 * L ^ 2)) := by
  have h0 : 0 < L := by linarith
  have hg : 1.436e-16 / L < 5.7410e-13 / L :=
    (div_lt_div_iff_of_pos_right h0).mpr (by norm_num)
  have hn : 0 ≤ 5.7410e-13 / L ^ 2 := by positivity
  have ht : 0 ≤ 5.7410e-13 / (2 * L ^ 2) := by positivity
  rw [mul_add, mul_one_div, mul_one_div]
  linarith

#print axioms envelope_identity
#print axioms point_term_le_printed
#print axioms envelope_gt_printed
end LeanLab.ChenExplicit.Decomp94b
