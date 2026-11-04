import LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp286b

theorem tau5_one : tau5 1 = 1 := by
  norm_num [tau5, pow_succ, ArithmeticFunction.mul_apply_one]