/- Unit U-1423, PC run 20261021T1403Z-5629: vacuity instances and axioms of U1423MVMinor. -/
import LeanLab.ExceptionalSet.U1423MVMinor

namespace LeanLab.ExceptionalSet.MV75U1423
open Real

/-- vacuity: `δ = 1/15` meets the hypotheses of `powerSaving_of_majorCount83`. -/
example : (0 : ℝ) < 1 / 15 ∧ (1 / 15 : ℝ) ≤ 1 / 15 := by norm_num

/-- vacuity: the major arcs at `x = 10`, `P = 10^{6/15}` contain `0`. -/
example : (0 : ZMod (LeanLab.ExceptionalSet.MV.Mx 10)) ∈ mvMajor 10 ((10 : ℝ) ^ (6 * (1 / 15 : ℝ))) :=
  zero_mem_mvMajor 10 (Real.one_le_rpow (by norm_num) (by norm_num))

/-- vacuity of `sub_rpow_ge_of_ge`: `n = X = 3`, `β = 1`. -/
example : Real.exp (-1) * ((1 - 1) * 3 * Real.log 3) ≤ (3 : ℝ) - (3 : ℝ) ^ (1 : ℝ) :=
  sub_rpow_ge_of_ge (by norm_num) le_rfl (by norm_num) le_rfl
    (by have : 0 < 1 / Real.log 3 := by positivity
        linarith)

/-- vacuity of `card_gcd_gt_le`: `X = 12`, `r = 6`, `D = 1`. -/
example : (((Finset.Ioc 0 12).filter (fun n : ℕ => (1 : ℝ) < (Nat.gcd n 6 : ℝ))).card : ℝ) ≤
    (12 : ℝ) * ((6 : ℕ).divisors.card : ℝ) / 1 :=
  card_gcd_gt_le 12 (by norm_num) one_pos

/-- vacuity of `div_totient_sq_le` at `r = 9`: `9/36 ≤ 4/3`. -/
example : ((9 : ℕ) : ℝ) / (Nat.totient 9 : ℝ) ^ 2 ≤ 4 / √((9 : ℕ) : ℝ) :=
  div_totient_sq_le (by norm_num)

#print axioms zero_mem_mvMajor
#print axioms minor_sup_P
#print axioms sqrt_P
#print axioms minor_sup_33
#print axioms log_pow10_le
#print axioms minorTerm_33
#print axioms mvInputs_of_majorCount83
#print axioms powerSaving_of_majorCount83
#print axioms theorem1_of_majorCount83
#print axioms one_sub_exp_neg_ge
#print axioms rpow_eq_exp
#print axioms sub_rpow_ge_of_ge
#print axioms sub_rpow_ge_of_lt
#print axioms card_gcd_gt_le
#print axioms div_totient_sq_le

end LeanLab.ExceptionalSet.MV75U1423
