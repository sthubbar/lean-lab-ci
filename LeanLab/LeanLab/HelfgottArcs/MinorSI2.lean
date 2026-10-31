/-
P0013 Helfgott, Minor arcs for Goldbach's problem, arXiv 1205.5252v4, Section 5.2,
pages 70 and 71: the bound for |S_I,2| when q > x^{1/3}/6, from Lemma 3.7 on page 26.
Read by curl and pdftotext, formulas checked on the rendered page images,
cloud session 20261018T1650Z-cloud2.

Page 70 sets V = x^{1/3}/3 and V = 2y, so y = x^{1/3}/6, and bounds the first line of (3.49),
(x/2q) min(1, 4c₀'/δ²) log(x^{1/3}q/3), by (x/2y) log(x^{1/3}y/3), then prints this as
(3/2) x^{2/3} ((2/3) log x − log 9). With y = x^{1/3}/6 the value is
3 x^{2/3} ((2/3) log x − log 18), larger by 3 x^{2/3}(log x^{1/3} − log 6) for x^{1/3} > 6.
`first_line_printed_too_small` proves this, writing t = x^{1/3}, x = t³.

Page 71 then states |S_I,2| ≤ 1213.15 x^{2/3} log x + 0.0006406 x^{2/3} (log x)², while
Lemma 3.7 bounds (3.48) by (3.49) PLUS (3.50) or (3.51), and the paper's own bounds are
(3/2) x^{2/3}((2/3) log x − log 9) + 0.02017 x^{2/3} log x for (3.49) and
1212.591 x^{2/3} log x + 29.131 x^{1/2} log x for (3.51). `printed_sum_exceeds_total` proves
that these two printed bounds alone add to more than 1213.15 x^{2/3} log x once log x ≥ 8.

Only arithmetic is proved here; whether the Main Theorem's 1218 survives is a QUESTION,
see STATEMENTS.md. AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.HelfgottArcs.MinorSI2
open Real

/-- The bound `(x/2y) log(x^{1/3} y / 3)` at `y = x^{1/3}/6`, with `t = x^{1/3}`. -/
noncomputable def firstLine (t : ℝ) : ℝ := t ^ 3 / (2 * (t / 6)) * Real.log (t * (t / 6) / 3)

/-- The printed value `(3/2) x^{2/3} ((2/3) log x − log 9)`, with `x = t³`. -/
noncomputable def firstLinePrinted (t : ℝ) : ℝ :=
  3 / 2 * t ^ 2 * (2 / 3 * Real.log (t ^ 3) - Real.log 9)

/-- The correct closed form, `3 x^{2/3} ((2/3) log x − log 18)`. -/
theorem firstLine_eq {t : ℝ} (ht : 0 < t) :
    firstLine t = 3 * t ^ 2 * (2 / 3 * Real.log (t ^ 3) - Real.log 18) := by
  unfold firstLine
  have e1 : t * (t / 6) / 3 = t ^ 2 / 18 := by ring
  have e2 : t ^ 3 / (2 * (t / 6)) = 3 * t ^ 2 := by field_simp; ring
  rw [e1, e2, Real.log_div (by positivity) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast; ring

/-- The difference is exactly `3 t² (log t − log 6)`. -/
theorem firstLine_sub {t : ℝ} (ht : 0 < t) :
    firstLine t - firstLinePrinted t = 3 * t ^ 2 * (Real.log t - Real.log 6) := by
  rw [firstLine_eq ht]
  unfold firstLinePrinted
  have h18 : Real.log 18 = 2 * Real.log 3 + Real.log 2 := by
    rw [show (18 : ℝ) = 3 ^ 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have h6 : Real.log 6 = Real.log 3 + Real.log 2 := by
    rw [show (6 : ℝ) = 3 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [Real.log_pow, h18, h9, h6]
  push_cast; ring

/-- For `x^{1/3} > 6`, in particular for every `x ≥ 2.16·10²⁰`, the printed bound is
smaller than the quantity it bounds. -/
theorem first_line_printed_too_small {t : ℝ} (ht : 6 < t) :
    firstLinePrinted t < firstLine t := by
  have h := firstLine_sub (by linarith : (0 : ℝ) < t)
  have hl : Real.log 6 < Real.log t := Real.log_lt_log (by norm_num) ht
  have : 0 < 3 * t ^ 2 * (Real.log t - Real.log 6) := by
    have : 0 < t ^ 2 := by positivity
    have : 0 < Real.log t - Real.log 6 := by linarith
    positivity
  linarith

/-- At `x₀ = 2.16·10²⁰`, `x₀^{1/3} = 6·10⁶`. -/
theorem x0_cube : ((6 : ℝ) * 10 ^ 6) ^ 3 = 2.16e20 := by norm_num

/-- The paper's two printed bounds, with `L = log x` and everything divided by
`x^{2/3}`, exceed the printed total once `L ≥ 8`; the `x^{1/2} log x` term is dropped,
which only helps the printed total. `log 9 < 2.2` is all that is used. -/
theorem printed_sum_exceeds_total {L : ℝ} (hL : 8 ≤ L) :
    1213.15 * L < 3 / 2 * (2 / 3 * L - Real.log 9) + 0.02017 * L + 1212.591 * L := by
  have h9 : Real.log 9 < 2.2 := by
    have := Real.log_two_lt_d9
    have h3 : Real.log 3 < 1.0987 := by
      have := Real.log_three_lt_d9 ; linarith
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  nlinarith

end LeanLab.HelfgottArcs.MinorSI2
