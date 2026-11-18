import LeanLab.ExceptionalSet.SPLIT_leaf_small_case

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

#check iteratedDerivWithin_eq_iteratedDeriv
#check uniqueDiffOn_Icc
#check tendsto_rpow_atTop
#check Complex.norm_le_abs_re_add_abs_im
#check Complex.exp_ofReal_mul_I_re

private theorem taylor_quadratic_test (t m : ℕ) (ht : 0 < t) (hm : 0 < m) (x : ℝ) :
    taylorWithinEval (fun z : ℝ => z ^ 2 / (t : ℝ) ^ 4) 2 (Set.Icc 0 m) 0 x =
      x ^ 2 / (t : ℝ) ^ 4 := by
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (m : ℝ)) := uniqueDiffOn_Icc (by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith)
  have hcf : ContDiffAt ℝ 2 (fun z : ℝ => z ^ 2 / (t : ℝ) ^ 4) 0 := by
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Icc 0 (m : ℝ) := ⟨by norm_num, by positivity⟩
  have h1 : iteratedDerivWithin 1 (fun z : ℝ => z ^ 2 / (t : ℝ) ^ 4) (Set.Icc 0 m) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (by fun_prop) hmem]
    simp [iteratedDeriv_succ']
  have h2 : iteratedDerivWithin 2 (fun z : ℝ => z ^ 2 / (t : ℝ) ^ 4) (Set.Icc 0 m) 0 =
      2 / (t : ℝ) ^ 4 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (by fun_prop) hmem]
    simp [iteratedDeriv_succ']
  rw [show (2 : ℕ) = 1 + 1 by norm_num, taylorWithinEval_succ, taylorWithinEval_succ,
    taylor_within_zero_eval]
  simp only [h1, h2, smul_eq_mul]
  ring

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
