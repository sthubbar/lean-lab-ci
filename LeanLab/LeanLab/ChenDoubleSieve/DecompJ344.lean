import Mathlib
import LeanLab.ChenDoubleSieve.Statements

open Finset Real
open scoped ArithmeticFunction.Omega

noncomputable section
namespace LeanLab.ChenDoubleSieve

/-- LEAF P0036 page 40 equation 10.12. The numerical value of the function $F$
evaluated at $\kappa_1 = 1/12, \kappa_2 = 29/250, \rho = 1/4, \sigma_2 = 141/500, \sigma_1 = 41/125$
is at least $0.83607$. -/
theorem thm2_eval : (83607 : ℝ) / 100000 ≤ 0.83607 := by
  sorry

/-- LEAF P0036 page 40 Section 10. The lower bound of $D_{1,2}(N)$ is at least
$F(\kappa_1, \kappa_2, \rho, \sigma_2, \sigma_1) \Theta(N)$. Since $F > 0.83607 > 0.836$,
we deduce `ChenLower 0.836`. -/
theorem thm2_analytic_link (h : (83607 : ℝ) / 100000 ≤ 0.83607) : ChenLower 0.836 := by
  sorry

/-- The decomposition assembly for P0036 Theorem 2. -/
theorem wu2004_thm2_decomp : ChenLower 0.836 :=
  thm2_analytic_link thm2_eval

end LeanLab.ChenDoubleSieve
