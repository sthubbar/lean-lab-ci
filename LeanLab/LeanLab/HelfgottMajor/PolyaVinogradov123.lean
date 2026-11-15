import Mathlib

/-!
Route burst 2026-11-15, step gaussian_explicit_estimate p5, a repair of the rejected p4 branch.
P0014 Helfgott, Major arcs for Goldbach's problem, page 36, display 4.20: the explicit
Pólya-Vinogradov inequality for M(q), the largest absolute value of a partial sum of χ(m).
The paper states display 4.20 without proof, so it is a citation wall and is not split: CITED-LEFT.
This file holds that one LEAF and nothing else. No definition is made: M(q) is written out as
the supremum over n of the norm of the sum of χ(m) for m from 1 to n.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real

/-- LEAF: P0014 display 4.20, page 36, the explicit Pólya-Vinogradov inequality for a primitive
character modulo q above 1. CITED-LEFT, the paper states it without proof.
QUESTION, typographical: both cases are printed with χ(−1) = 1; the second case is read here as
χ(−1) different from 1, that is χ odd. -/
theorem polya_vinogradov_4_20 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      if χ (-1) = 1 then
        2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q
      else
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  sorry

end LeanLab.HelfgottMajor.PolyaVinogradov123
