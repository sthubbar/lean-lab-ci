/-
Helfgott book https://arxiv.org/abs/1501.05438 pages 267 and 268.
The explicit integral envelopes used in equation 14.28.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Helfgott2013.SectionSevenH

namespace LeanLab.Ternary.Task580
open MeasureTheory

/-- The two piece explicit envelope has the book C zero budget.
Helfgott book page 267 display for C eta plus zero before equation 14.28.
This evaluates the envelope integrals and asserts no bound for eta plus itself. -/
theorem book_C0_envelope :
    (0.7131 : ℝ) *
      ((∫ t in Set.Ioc (0 : ℝ) 1, 1.07996 ^ 2 * t ^ (-(1 / 2 : ℝ))) +
        ∫ t in Set.Ioi (1 : ℝ), 1.19073 ^ 2 * t ^ (-(5 / 2 : ℝ))) ≤ 2.33744 := by
  rw [integral_const_mul, integral_const_mul,
    LeanLab.Helfgott2013.SectionSevenH.int_rpow_half,
    LeanLab.Helfgott2013.SectionSevenH.int_rpow_five_half]
  norm_num

/-- The logarithmic explicit envelope has the book C one budget.
Helfgott book page 267 display for C eta plus one before equation 14.28.
The existing exact logarithmic power integral supplies the analytic identity. -/
theorem book_C1_envelope :
    (0.7131 : ℝ) *
      (∫ t in Set.Ioi (1 : ℝ),
        1.19073 ^ 2 * (Real.log t * t ^ (-(5 / 2 : ℝ)))) ≤ 0.44937 := by
  rw [integral_const_mul, LeanLab.Helfgott2013.SectionSevenH.int_log_rpow_five_half]
  norm_num

/-- The rounded uniform envelope has the corrected book C two budget.
Helfgott book page 268 display before equation 14.28, using the rounded
1.07996 envelope from the preceding page. -/
theorem book_C2_envelope : (0.51942 : ℝ) * 1.07996 ^ 2 ≤ 0.60581 := by
  norm_num

end LeanLab.Ternary.Task580
