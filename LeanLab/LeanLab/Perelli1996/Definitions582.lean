/-
Perelli 1996, pages 486 and 487, equations 27 and 31.
Unchanged remainder definitions moved from Decomp289a to break the supply cycle.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.DecompJ228
import LeanLab.Perelli1996.Definitions103

namespace LeanLab.Perelli1996.Decomp289a
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88
noncomputable section

/-- The order Q of the Section 3 dissection on page 486. -/
def meanOrder (F : ℤ[X]) (N H B : ℝ) : ℝ :=
  H ^ F.natDegree * Real.log N ^ (-B)

/-- The nonnegative remainder sum Sigma P below equation 27 on page 486.
Reduced residues use representatives one through q, as in the paper.
The existing characterRemainder uses an inclusive cutoff with a zero term
in its principal kernel. This is the endpoint variant of the printed sum. -/
def remainderMass (F : ℤ[X]) (c N H B : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
    ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
      ∫ η in Set.Icc (-(1 / ((q : ℝ) * meanOrder F N H B)))
        (1 / ((q : ℝ) * meanOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q (a : ℤ) η‖ ^ 2

/-- The remainder mass is nonnegative, as a sum of squared norms. -/
theorem remainderMass_nonneg (F : ℤ[X]) (c N H B : ℝ) :
    0 ≤ remainderMass F c N H B := by
  unfold remainderMass
  positivity

end
end LeanLab.Perelli1996.Decomp289a
