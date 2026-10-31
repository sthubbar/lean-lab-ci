import LeanLab.RieselVaughan1983.Decomp93
import LeanLab.RieselVaughan1983.Lemma4From393

/-! Exact inputs needed for the weighted lower leaf.
AI wrote the Lean code. Binary Goldbach is OPEN.
No numerical bracket is assumed silently. -/
namespace LeanLab.RieselVaughan1983.WeightedLower93
open Real
open Lemma4From393
noncomputable section

/-- Page 54 lower form of Lemma 4, conditional on equation 3.14 and the
four one-sided brackets from page 47 equations 2.20 to 2.22. -/
theorem weighted_lower_of (h3 : Lemma3.Lemma3ApproxP)
    (h6 : 8463433 / 1000000 ≤ A6 (3 / 2))
    (h7 : -(9260623 / 1000000) ≤ A7 (3 / 2))
    (h8 : A8 (3 / 2) ≤ 9310077 / 1000)
    (h9 : A9 (3 / 2) ≤ 2950889 / 100000)
    (x : ℝ) (hx : exp 24 ≤ x) :
    Decomp93.lowerPolynomial x < 8 * Ctw * Lemma3.S2 (sqrt (2 / 3 * x)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos _) hx
  have hx25 : (25 : ℝ) ≤ x := by linarith [add_one_le_exp (24 : ℝ)]
  have hl : 0 ≤ log x := log_nonneg (by linarith)
  have h := (abs_lt.mp (lemma4_of h3 x (3 / 2) (by norm_num) (by linarith))).1
  rw [show x / (3 / 2) = 2 / 3 * x by ring] at h
  have h6x := mul_le_mul_of_nonneg_right h6 hl
  have h8x := mul_le_mul_of_nonneg_right h8 (rpow_nonneg hx0.le (-(1 / 6 : ℝ)))
  have h9x := mul_le_mul_of_nonneg_right h9 (rpow_nonneg hx0.le (-(1 / 2 : ℝ)))
  unfold Decomp93.lowerPolynomial
  linarith

end
end LeanLab.RieselVaughan1983.WeightedLower93

#print axioms LeanLab.RieselVaughan1983.WeightedLower93.weighted_lower_of
