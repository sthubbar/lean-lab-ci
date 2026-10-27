/-
P0083, pages 477 and 478. The original declarations are in Definitions88.
The cited theorem is assembled in Decomp88 from named analytic leaves.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Definitions88
import LeanLab.Perelli1996.Decomp88

namespace LeanLab.Perelli1996
noncomputable section

/-- Cited. P0083 Theorem 1. -/
theorem perelli_theorem1 : Theorem1 := Decomp88.theorem1

/-- P0083 Corollary 1, second assertion, CONDITIONAL ON the cited Theorem 1 only.
AI wrote this derivation through the definitionally equal B encoding. -/
theorem perelli_cor1b : Cor1b := B.cor1b_of perelli_theorem1

end

end LeanLab.Perelli1996
