/- AI wrote this Lean code for CODEX task224. Goldbach is open.
Published numerical theta input for journal p. 1220 display 4.
https://arxiv.org/abs/2002.11068 Theorem 1 and Table 15 p. 33. -/
import Mathlib

namespace LeanLab.BS2022GRH.ThetaInputs224
open Real

/-- LEAF. Broadbent et al. Theorem 1 and Table 15 p. 33, row 2500.
Both one-sided k equal to one constants are 2.2885e-9.
The table and its computational analytic proof remain cited inputs. -/
theorem theta_table15_2500 (x : ℝ) (hx : exp 2500 < x) :
    |Chebyshev.theta x - x| ≤ 2.2885e-9 * x / log x := by
  sorry

/-- LEAF. Broadbent et al. Theorem 1 and Table 15 p. 32, row log of 6e11.
The common k equal to one constant is 6.9322e-5. -/
theorem theta_table15_6e11 (x : ℝ) (hx : 6e11 < x) :
    |Chebyshev.theta x - x| ≤ 6.9322e-5 * x / log x := by
  sorry

/-- LEAF. Broadbent et al. Theorem 1 and Table 15 p. 32, row 37.
The common k equal to one constant is 8.6315e-7. -/
theorem theta_table15_37 (x : ℝ) (hx : exp 37 < x) :
    |Chebyshev.theta x - x| ≤ 8.6315e-7 * x / log x := by
  sorry

/-- LEAF. Buthe 2018 Theorem 2, p. 2 display 1.7.
https://arxiv.org/abs/1511.02032. The verified computation reaches 1e19. -/
theorem theta_buthe_1e19 (x : ℝ) (hx : 1 ≤ x) (hx1 : x ≤ 1e19) :
    (0.05 : ℝ) * sqrt x < x - Chebyshev.theta x := by
  sorry

end LeanLab.BS2022GRH.ThetaInputs224
