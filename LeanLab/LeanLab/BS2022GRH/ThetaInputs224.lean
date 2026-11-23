/- AI wrote this Lean code for CODEX task224. Goldbach is open.
Published numerical theta input for journal p. 1220 display 4.
https://arxiv.org/abs/2002.11068 Theorem 1 and Table 15 p. 33. -/
import Mathlib
import LeanLab.BS2022GRH.ThetaLeavesS63

namespace LeanLab.BS2022GRH.ThetaInputs224
open Real

/-- LEAF. Buthe 2018 Theorem 2, p. 2 display 1.7.
https://arxiv.org/abs/1511.02032. The verified computation reaches 1e19. -/
theorem theta_buthe_1e19 (x : ℝ) (hx : 1 ≤ x) (hx1 : x ≤ 1e19) :
    (0.05 : ℝ) * sqrt x < x - Chebyshev.theta x := by
  sorry

/-- LEAF. Broadbent et al. Theorem 1 and Table 15 p. 33, row 2500.
Both one-sided k equal to one constants are 2.2885e-9.
The table and its computational analytic proof remain cited inputs. -/
theorem theta_table15_2500 (x : ℝ) (hx : exp 2500 < x) :
    |Chebyshev.theta x - x| ≤ 2.2885e-9 * x / log x := by
  -- S63: from the corrected Broadbent et al. 2026 Table 2 row 2500, eta1 = 2.6726e-10.
  have h1 : (1 : ℝ) < x := lt_trans (one_lt_exp_iff.mpr (by norm_num)) hx
  exact ThetaLeavesS63.abs_le_of_row x _ _ h1 (by norm_num)
    (ThetaLeavesS63.broadbent2026_row2500 x hx)

/-- LEAF. Broadbent et al. Theorem 1 and Table 15 p. 32, row log of 6e11.
The common k equal to one constant is 6.9322e-5. -/
theorem theta_table15_6e11 (x : ℝ) (hx : 6e11 < x) :
    |Chebyshev.theta x - x| ≤ 6.9322e-5 * x / log x := by
  -- S63: Buthe 2018 displays 1.6 and 1.7 up to 1e19, corrected 2026 row 40 above.
  rcases le_or_gt x 1e19 with h19 | h19
  · exact ThetaLeavesS63.abs_le_of_sqrt_bounds x _ (by linarith)
      (by nlinarith [theta_buthe_1e19 x (by linarith) h19, Real.sqrt_nonneg x])
      (ThetaLeavesS63.buthe2018_display16 x (by linarith) h19)
      (ThetaLeavesS63.anchor_6e11 x hx.le)
  · exact ThetaLeavesS63.abs_le_of_row x _ _ (by linarith) (by norm_num)
      (ThetaLeavesS63.broadbent2026_row40 x (ThetaLeavesS63.exp40_lt_1e19.trans h19))

/-- LEAF. Broadbent et al. Theorem 1 and Table 15 p. 32, row 37.
The common k equal to one constant is 8.6315e-7. -/
theorem theta_table15_37 (x : ℝ) (hx : exp 37 < x) :
    |Chebyshev.theta x - x| ≤ 8.6315e-7 * x / log x := by
  -- S63: Buthe 2018 displays 1.6 and 1.7 up to 1e19, corrected 2026 row 40 above.
  have h37 := ThetaLeavesS63.exp_37_ge
  rcases le_or_gt x 1e19 with h19 | h19
  · exact ThetaLeavesS63.abs_le_of_sqrt_bounds x _ (by linarith)
      (by nlinarith [theta_buthe_1e19 x (by linarith) h19, Real.sqrt_nonneg x])
      (ThetaLeavesS63.buthe2018_display16 x (by linarith) h19)
      (ThetaLeavesS63.anchor_37 x hx)
  · exact ThetaLeavesS63.abs_le_of_row x _ _ (by linarith) (by norm_num)
      (ThetaLeavesS63.broadbent2026_row40 x (ThetaLeavesS63.exp40_lt_1e19.trans h19))

end LeanLab.BS2022GRH.ThetaInputs224

#print axioms LeanLab.BS2022GRH.ThetaInputs224.theta_table15_2500
#print axioms LeanLab.BS2022GRH.ThetaInputs224.theta_table15_6e11
#print axioms LeanLab.BS2022GRH.ThetaInputs224.theta_table15_37
