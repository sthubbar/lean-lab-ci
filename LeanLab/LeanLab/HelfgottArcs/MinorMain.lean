/-
P0013 Helfgott, Minor arcs for Goldbach's problem, arXiv 1205.5252v4: the Main Theorem's
case q > x^{1/3}/6, |S_η(α, x)| ≤ 0.2727 x^{5/6}(log x)^{3/2} + 1218 x^{2/3} log x for
x ≥ x₀ = 2.16·10²⁰, as assembled in (5.61) on page 72 from the paper's own pieces:
|S_I,1| ≤ 4.1982 x^{2/3} log x + 0.001063 x^{2/3}(log x)² (page 70),
the (3.51) part of |S_I,2| ≤ 1213.15 x^{2/3} log x (page 71, the paper's own figure),
the (3.49) part of |S_I,2|, and |S_II| ≤ 0.272652 x^{5/6}(log x)^{3/2} (5.60).

Everything is divided by x^{2/3} log x; at x₀, x^{1/6} = s = 1000√6 and L = log x₀.
With (3.49) as printed, (3/2)((2/3)L − log 9)/L + 0.02017, the sum fits: `printed_fits`.
With (3.49) as its own formula gives it at y = x^{1/3}/6, 3((2/3)L − log 18)/L + 0.02017,
see MinorSI2.lean, the sum exceeds the Main Theorem's bound at x₀ by more than 0.4:
`corrected_exceeds`. So the paper's argument does not reach the constant 1218 at x₀; this
is a gap in the proof of the stated constant, not a proof that the inequality is false.

AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.HelfgottArcs.MinorMain
open Real

/-- `L = log x₀ = 18 log 10 + 3 log 6`, as `x₀ = 10¹⁸ · 6³`. -/
theorem L_eq : Real.log 2.16e20 = 18 * Real.log 10 + 3 * Real.log 6 := by
  rw [show (2.16e20 : ℝ) = 10 ^ 18 * 6 ^ 3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast; ring

theorem log10_lt : Real.log 10 < 2.3105 := by
  have h : Real.log (10 ^ 3) < Real.log (2 ^ 10) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  have := Real.log_two_lt_d9
  push_cast at h; linarith

theorem log10_gt : 2.282 < Real.log 10 := by
  have h : Real.log (2 ^ 5 * 3) < Real.log (10 ^ 2) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow] at h
  have := Real.log_two_gt_d9
  have := Real.log_three_gt_d9
  push_cast at h; linarith

theorem log6_bounds : 1.7917 < Real.log 6 ∧ Real.log 6 < 1.7918 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have := Real.log_two_gt_d9; have := Real.log_two_lt_d9
  have := Real.log_three_gt_d9; have := Real.log_three_lt_d9
  constructor <;> linarith

theorem L_bounds : 46.45 < Real.log 2.16e20 ∧ Real.log 2.16e20 < 47 := by
  rw [L_eq]
  have := log10_lt; have := log10_gt; have := log6_bounds
  constructor <;> linarith

theorem s_bounds : 2449 < 1000 * Real.sqrt 6 ∧ 1000 * Real.sqrt 6 < 2449.5 := by
  have h1 : (2.449 : ℝ) < Real.sqrt 6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 6 < 2.4495 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith

theorem log18_lt : Real.log 18 < 2.8904 := by
  rw [show (18 : ℝ) = 2 * 3 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  have := Real.log_two_lt_d9; have := Real.log_three_lt_d9
  push_cast; linarith

theorem log9_lt : Real.log 9 < 2.1973 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
  have := Real.log_three_lt_d9
  push_cast; linarith

/-- The sum of the paper's pieces, per unit `x^{2/3} log x`, with a given (3.49) part. -/
noncomputable def total (L s part349 : ℝ) : ℝ :=
  4.1982 + 0.001063 * L + part349 + 1213.15 + 0.272652 * s * Real.sqrt L

/-- The Main Theorem's bound per unit `x^{2/3} log x`. -/
noncomputable def target (L s : ℝ) : ℝ := 1218 + 0.2727 * s * Real.sqrt L

theorem printed_fits_of {L s : ℝ} (hL1 : 46.45 < L) (hL2 : L < 47) (hs1 : 2449 < s) :
    total L s (3 / 2 * (2 / 3 * L - Real.log 9) / L + 0.02017) < target L s := by
  have h9 := log9_lt
  have hsq : (6.8 : ℝ) < Real.sqrt L := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have hL0 : 0 < L := by linarith
  have hp : 2449 * 6.8 < s * Real.sqrt L := mul_lt_mul hs1 hsq.le (by norm_num) (by linarith)
  have hdiv : 3 / 2 * Real.log 9 / L < 0.08 := by
    rw [div_lt_iff₀ hL0]; nlinarith
  have e : 3 / 2 * (2 / 3 * L - Real.log 9) / L = 1 - 3 / 2 * Real.log 9 / L := by
    field_simp
  have hd0 : 0 ≤ 3 / 2 * Real.log 9 / L := by
    have : 0 < Real.log 9 := Real.log_pos (by norm_num)
    positivity
  unfold total target
  rw [e, show 0.272652 * s * Real.sqrt L = 0.272652 * (s * Real.sqrt L) by ring,
    show 0.2727 * s * Real.sqrt L = 0.2727 * (s * Real.sqrt L) by ring]
  linarith

/-- With (3.49) as printed on page 70, the pieces fit under the Main Theorem at `x₀`. -/
theorem printed_fits :
    total (Real.log 2.16e20) (1000 * Real.sqrt 6)
      (3 / 2 * (2 / 3 * Real.log 2.16e20 - Real.log 9) / Real.log 2.16e20 + 0.02017) <
    target (Real.log 2.16e20) (1000 * Real.sqrt 6) :=
  printed_fits_of L_bounds.1 L_bounds.2 s_bounds.1

theorem corrected_exceeds_of {L s : ℝ} (hL1 : 46.45 < L) (hL2 : L < 47) (hs1 : 0 < s)
    (hs2 : s < 2449.5) :
    target L s + 0.4 < total L s (3 * (2 / 3 * L - Real.log 18) / L + 0.02017) := by
  have h18 := log18_lt
  have hsq : Real.sqrt L < 6.86 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  have hL0 : 0 < L := by linarith
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hp : s * Real.sqrt L < 2449.5 * 6.86 := by
    calc s * Real.sqrt L ≤ s * 6.86 := mul_le_mul_of_nonneg_left hsq.le hs1.le
      _ < 2449.5 * 6.86 := by nlinarith
  have hdiv : 3 * Real.log 18 / L < 0.19 := by
    rw [div_lt_iff₀ hL0]; nlinarith
  have e : 3 * (2 / 3 * L - Real.log 18) / L = 2 - 3 * Real.log 18 / L := by
    field_simp
  unfold total target
  rw [e, show 0.272652 * s * Real.sqrt L = 0.272652 * (s * Real.sqrt L) by ring,
    show 0.2727 * s * Real.sqrt L = 0.2727 * (s * Real.sqrt L) by ring]
  linarith

/-- With (3.49) as its formula gives it at `y = x^{1/3}/6`, the pieces exceed the Main
Theorem's bound at `x₀` by more than 0.4 units of `x^{2/3} log x`. -/
theorem corrected_exceeds :
    target (Real.log 2.16e20) (1000 * Real.sqrt 6) + 0.4 <
    total (Real.log 2.16e20) (1000 * Real.sqrt 6)
      (3 * (2 / 3 * Real.log 2.16e20 - Real.log 18) / Real.log 2.16e20 + 0.02017) :=
  corrected_exceeds_of L_bounds.1 L_bounds.2 (by linarith [s_bounds.1]) s_bounds.2

end LeanLab.HelfgottArcs.MinorMain
