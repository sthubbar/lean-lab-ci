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

/-- The multiplicity weighted zero count at height one as the finite sum over the
nontrivial zeros of height at most one: the `tsum` defining `zeroCount` is an indicator
function of `ZeroCount1623.stripZeros`, whose support is finite. -/
private lemma zero_count_one_eq_sum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    zeroCount χ 1 = ∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ 1).toFinset,
      (ZeroCount1623.mult χ ρ : ℝ) := by
  rw [zeroCount]
  simp only [zeroWeight, ZeroCount1623.mult]
  rw [← tsum_subtype {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1}
    (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))]
  exact ZeroCount1623.tsum_zeroIdx χ 1
    (fun z => (ZeroCount1623.mult χ z : ℝ))

/-- The height one counting input: `ZeroCount1623.zero_count_two_sided` at `T = 1` bounds
the multiplicity weighted nontrivial zeros of height at most one by the main term
`log (q / (2 π e)) / π` plus the height one error `0.3 log q + 6.778`.  This is the sharp
form of the input: the one sided count of display 4.26 carries only half the main term,
and the three conductor ranges below cannot afford that loss. -/
private lemma zero_count_one_book (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    zeroCount χ 1 ≤ 1 / π * (log (q : ℝ) - log (2 * π * exp 1)) + 0.3 * log (q : ℝ) + 6.778 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have h := (abs_le.mp (ZeroCount1623.zero_count_two_sided χ hχ (T := 1) le_rfl)).2
  have hmain : 2 * ZeroCount1623.bookMain q 1
      = 1 / π * log ((q : ℝ) * 1 / (2 * π * exp 1)) := by
    unfold ZeroCount1623.bookMain
    have h2 : (1 : ℝ) / (2 * π) = (1 / 2) * (1 / π) := by
      rw [one_div, one_div, one_div, mul_inv]
    rw [h2]
    ring
  have herr : 2 * ZeroCount1623.bookError q 1 = 0.3 * log ((q : ℝ) * 1) + 6.778 := by
    unfold ZeroCount1623.bookError
    ring
  rw [hmain, herr] at h
  simp only [mul_one] at h
  rw [log_div hq0.ne' (by positivity)] at h
  rw [zero_count_one_eq_sum (q := q) χ]
  linarith

/-- LEAF. Short conductors, `q ≤ 2 * π`.  Here the main term of the count is at most
`-1 / π`, more precisely `log (q / (2 * π * exp 1)) / π` is at most
`-log (2 * π * exp 1) / π` because `log q ≥ 0`, so the count is bounded by the height
half of the logarithmic term, the constant `17.7`, and the negative constant
`-log (2 * π * exp 1) / π`. -/
theorem zero_count_one_short_q (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : (q : ℝ) ≤ 2 * π) :
    zeroCount χ 1 ≤ 0.5 * log (q : ℝ) + 17.7 - 1 / π * log (2 * π * exp 1) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le
  have hlq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hpi : 1 / π ≤ 0.319 := by
    rw [div_le_iff₀ pi_pos]
    nlinarith [pi_gt_d20]
  have hx : 1 / π * log (q : ℝ) ≤ 0.319 * log (q : ℝ) :=
    mul_le_mul_of_nonneg_right hpi hlq
  have hx8 : log (q : ℝ) ≤ 8 := by
    have h1 := log_le_sub_one_of_pos hq0
    have h2 : (q : ℝ) ≤ 8 := by nlinarith [pi_lt_four]
    linarith
  have hb := zero_count_one_book q χ hχ
  have hexp : 1 / π * (log (q : ℝ) - log (2 * π * exp 1))
      = 1 / π * log (q : ℝ) - 1 / π * log (2 * π * exp 1) := by ring
  rw [hexp] at hb
  linarith

/-- LEAF. Middle conductors, `2 * π ≤ q ≤ 2 * π * exp 1`.  On this range the main term
`log (q / (2 * π * exp 1)) / π` lies between `-1 / π` and `0`, so it is replaced by the
floor `-1 / π` of that range and the count is bounded by the height half of the
logarithmic term, the constant `17.7`, and `-1 / π`. -/
theorem zero_count_one_mid_q (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hlo : 2 * π ≤ (q : ℝ)) (hhi : (q : ℝ) ≤ 2 * π * exp 1) :
    zeroCount χ 1 ≤ 0.5 * log (q : ℝ) + 17.7 - 1 / π := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le
  have hlq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hpi : 1 / π ≤ 0.319 := by
    rw [div_le_iff₀ pi_pos]
    nlinarith [pi_gt_d20]
  have hx : 1 / π * log (q : ℝ) ≤ 0.319 * log (q : ℝ) :=
    mul_le_mul_of_nonneg_right hpi hlq
  have hx24 : log (q : ℝ) ≤ 24 := by
    have h1 := log_le_sub_one_of_pos hq0
    have h2 : (q : ℝ) ≤ 24 := by
      have h8 : 2 * π ≤ 8 := by nlinarith [Real.pi_lt_four]
      have he3 : exp (1 : ℝ) ≤ 3 := le_of_lt Real.exp_one_lt_three
      have hm := mul_le_mul h8 he3 (le_of_lt (Real.exp_pos 1)) (by positivity)
      linarith
    linarith
  have hc : 0 ≤ 1 / π * log (2 * π * exp 1) :=
    mul_nonneg (by positivity)
      (log_nonneg (by nlinarith [Real.pi_gt_three, Real.exp_one_gt_d9]))
  have hb := zero_count_one_book q χ hχ
  have hexp : 1 / π * (log (q : ℝ) - log (2 * π * exp 1))
      = 1 / π * log (q : ℝ) - 1 / π * log (2 * π * exp 1) := by ring
  rw [hexp] at hb
  linarith

/-- LEAF. Long conductors, `2 * π * exp 1 ≤ q`.  This leaf keeps the main term in full
and carries the counting of the multiplicity weighted zeros of height at most one for a
primitive character, together with the archimedean contribution and the halving of the
height term: no part of the printed bound is dropped on this range. -/
theorem zero_count_one_tall_q (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π * exp 1 ≤ (q : ℝ)) :
    zeroCount χ 1 ≤ 1 / π * log ((q : ℝ) / (2 * π * exp 1)) + 0.5 * log (q : ℝ) + 17.7 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hlq : 0 ≤ log (q : ℝ) := by
    refine log_nonneg ?_
    nlinarith [hq, Real.pi_gt_three, Real.exp_one_gt_d9]
  have hsplit : log ((q : ℝ) / (2 * π * exp 1))
      = log (q : ℝ) - log (2 * π * exp 1) := log_div hq0.ne' (by positivity)
  have hb := zero_count_one_book q χ hχ
  have hexp : 1 / π * (log (q : ℝ) - log (2 * π * exp 1))
      = 1 / π * log (q : ℝ) - 1 / π * log (2 * π * exp 1) := by ring
  rw [hexp] at hb
  rw [hsplit]
  linarith

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
