/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3, page 3, the factor e^(-γ) in U_N.
SPLIT of exp_neg_euler_gt, ROUTE BURST S98 burst-20261122.
AI wrote this Lean code.
-/
import LeanLab.JohnstonStarichkova.SPLIT_sifted_count_lower_v3

namespace LeanLab.JohnstonStarichkova
open LeanLab.AlmostPrimes

/-
Numerics: γ = 0.5772156649..., so γ < 0.57722 with margin 4.3e-6.
Then e^0.57722 = 1.7810801 < 1/0.56145 = 1.7811025.
-/
/-- LEAF: P0019 v3 page 3 uses the Euler constant γ = 0.5772156649; the upper
bound γ < 0.57722, e.g. from H_n - log n - 1/(2n) + 1/(12n^2) decreasing to γ,
an Euler Maclaurin bound at moderate n. Class MEDIUM. -/
theorem euler_lt_057722 : Real.eulerMascheroniConstant < (0.57722 : ℝ) := by
  sorry

/-- Exp step: e^0.57722 < 1/0.56145, by the degree 12 Taylor bound. -/
theorem exp_057722_lt : Real.exp (0.57722 : ℝ) < 1 / 0.56145 := by
  have h := Real.exp_bound' (x := (0.57722 : ℝ)) (by norm_num) (by norm_num) (n := 12)
    (by norm_num)
  refine lt_of_le_of_lt h ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

theorem exp_neg_euler_gt_split :
    (0.56145 : ℝ) < Real.exp (-Real.eulerMascheroniConstant) := by
  have h1 : Real.exp (-(0.57722 : ℝ)) < Real.exp (-Real.eulerMascheroniConstant) :=
    Real.exp_lt_exp.mpr (by linarith [euler_lt_057722])
  have h2 : (0.56145 : ℝ) < Real.exp (-(0.57722 : ℝ)) := by
    rw [Real.exp_neg]
    have hp := Real.exp_pos (0.57722 : ℝ)
    have h3 := exp_057722_lt
    rw [lt_inv_comm₀ (by norm_num) hp]
    calc Real.exp 0.57722 < 1 / 0.56145 := h3
      _ = (0.56145 : ℝ)⁻¹ := by norm_num
  linarith

end LeanLab.JohnstonStarichkova
