import LeanLab.HelfgottMajor.SPLIT_leaf_very_low_zero_count

/-!
Split of `zero_count_one_bound` in `HelfgottMajor.SPLIT_leaf_very_low_zero_count`.

The target is the height one instance of the explicit multiplicity weighted zero count
for a primitive `L`-function of conductor `q`:
`zeroCount χ 1 ≤ log (q / (2 * π * exp 1)) / π + log q / 2 + 17.7`.

The split cuts the single inequality along the two thresholds at which the logarithmic
main term `log (q / (2 * π * exp 1)) / π` changes sign, that is `q = 2 * π` and
`q = 2 * π * exp 1`.  On the two lower ranges that main term is at most `0` and at most
`-1 / π`, so the corresponding leaf keeps only that much of it and drops the positive
term `log q / π`, which is what makes those two ranges cheap.  On the upper range the
main term is nonnegative and cannot be dropped, so that leaf keeps it in full; it is the
range on which the counting input lives, and everything above `q = 2 * π * exp 1` is
that one leaf.  The assembly below is the case split plus the arithmetic comparison that
turns each leaf into the printed form.

`1 / π * log (q / (2 * π * exp 1))` is bounded below by `-1 / π` on the middle range and
by its own value on the upper range, so no leaf repeats the arithmetic of another.
-/

namespace LeanLab.HelfgottMajor.DecompJ1233
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389a Decomp388a

/-- LEAF. Short conductors, `q ≤ 2 * π`.  Here the main term of the count is at most
`-1 / π`, more precisely `log (q / (2 * π * exp 1)) / π` is at most
`-log (2 * π * exp 1) / π` because `log q ≥ 0`, so the count is bounded by the height
half of the logarithmic term, the constant `17.7`, and the negative constant
`-log (2 * π * exp 1) / π`. -/
theorem zero_count_one_short_q (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : (q : ℝ) ≤ 2 * π) :
    zeroCount χ 1 ≤ 0.5 * log (q : ℝ) + 17.7 - 1 / π * log (2 * π * exp 1) := by
  sorry

/-- LEAF. Middle conductors, `2 * π ≤ q ≤ 2 * π * exp 1`.  On this range the main term
`log (q / (2 * π * exp 1)) / π` lies between `-1 / π` and `0`, so it is replaced by the
floor `-1 / π` of that range and the count is bounded by the height half of the
logarithmic term, the constant `17.7`, and `-1 / π`. -/
theorem zero_count_one_mid_q (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hlo : 2 * π ≤ (q : ℝ)) (hhi : (q : ℝ) ≤ 2 * π * exp 1) :
    zeroCount χ 1 ≤ 0.5 * log (q : ℝ) + 17.7 - 1 / π := by
  sorry

/-- LEAF. Long conductors, `2 * π * exp 1 ≤ q`.  This leaf keeps the main term in full
and carries the counting of the multiplicity weighted zeros of height at most one for a
primitive character, together with the archimedean contribution and the halving of the
height term: no part of the printed bound is dropped on this range. -/
theorem zero_count_one_tall_q (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π * exp 1 ≤ (q : ℝ)) :
    zeroCount χ 1 ≤ 1 / π * log ((q : ℝ) / (2 * π * exp 1)) + 0.5 * log (q : ℝ) + 17.7 := by
  sorry

/-- Arithmetic of the short range: the main term at `log q = 0` plus the nonnegative
term `log q / π` is no more than the main term itself. -/
private lemma arith_short (x c : ℝ) (hx : 0 ≤ x) :
    0.5 * x + 17.7 - 1 / π * c ≤ 1 / π * (x - c) + 0.5 * x + 17.7 := by
  have hx' : 0 ≤ 1 / π * x := mul_nonneg (div_nonneg zero_le_one pi_pos.le) hx
  have h : 1 / π * (x - c) = 1 / π * x - 1 / π * c := by ring
  linarith

/-- Arithmetic of the middle range: the main term is bounded below by `-1 / π` there. -/
private lemma arith_mid (x c : ℝ) (h : -1 ≤ x - c) :
    0.5 * x + 17.7 - 1 / π ≤ 1 / π * (x - c) + 0.5 * x + 17.7 := by
  have hm : 1 / π * (-1) ≤ 1 / π * (x - c) :=
    mul_le_mul_of_nonneg_left h (div_nonneg zero_le_one pi_pos.le)
  have hone : 1 / π * (-1 : ℝ) = -(1 / π) := by ring
  linarith

/-- The height one bound, assembled from the three conductor ranges. -/
theorem zero_count_one_bound_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    zeroCount χ 1 ≤ 1 / π * log ((q : ℝ) / (2 * π * exp 1)) + 0.5 * log (q : ℝ) + 17.7 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hlq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hsplit : log ((q : ℝ) / (2 * π * exp 1)) = log (q : ℝ) - log (2 * π * exp 1) :=
    log_div hq0.ne' (by positivity)
  rcases le_total (q : ℝ) (2 * π) with h1 | h1
  · have hleaf := zero_count_one_short_q q χ hχ h1
    rw [hsplit]
    linarith [arith_short (log (q : ℝ)) (log (2 * π * exp 1)) hlq]
  · rcases le_total (q : ℝ) (2 * π * exp 1) with h2 | h2
    · have hleaf := zero_count_one_mid_q q χ hχ h1 h2
      have hC : log (2 * π * exp 1) = log (2 * π) + 1 := by
        rw [log_mul (by positivity) (exp_pos 1).ne', log_exp]
      have hl2 : log (2 * π) ≤ log (q : ℝ) := log_le_log (by positivity) h1
      have hL : -1 ≤ log (q : ℝ) - log (2 * π * exp 1) := by
        rw [hC]; linarith
      rw [hsplit]
      linarith [arith_mid (log (q : ℝ)) (log (2 * π * exp 1)) hL]
    · exact zero_count_one_tall_q q χ hχ h2

end LeanLab.HelfgottMajor.DecompJ1233
