/-
Exact upstream supply for the page 17 maximal prime distribution statement.
Davenport chapter 28 pages 161 and 162 and the page 17 prime counting form.
Source https://arxiv.org/abs/0801.0130
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp557b
import LeanLab.KumchevLiu2007.Bridge557

namespace LeanLab.KumchevLiu2007.Task557c

open scoped BigOperators

/-- Page 17 between displays 57 and 58. This is the exact maximal prime
statement with definitionally identical upstream numerical definitions.
CONDITIONAL ON the three named analytic leaves in Decomp557a and Decomp557b.
This assembly has no admission of its own and does not import Decomp542a. -/
theorem maximal_bombieri_vinogradov (A : ℝ) (hA : 0 < A) :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 < C ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T → ∀ D : ℕ,
        (D : ℝ) ≤ Real.sqrt T * Real.log T ^ (-b) →
        (∑ d ∈ Finset.Icc 1 D, primeError T d) ≤
          C * T * Real.log T ^ (-A) := by
  apply maximal_prime_of_discrete ?_ A hA
  have hPi := LeanLab.PNTPort.BVMax.bvPi_of
    (LeanLab.PNTPort.BVMax.bvTheta_of Task557b.maximal_psi_bv)
  simpa only [LeanLab.PNTPort.BVMax.BVPi, LeanLab.PNTPort.BVMax.piAP,
    LeanLab.PNTPort.BVMax.piN, LeanLab.PNTPort.BVMax.liD,
    LeanLab.PNTPort.BVMax.liN, primeAP, discreteLi, and_comm] using hPi

#print axioms maximal_bombieri_vinogradov

end LeanLab.KumchevLiu2007.Task557c
