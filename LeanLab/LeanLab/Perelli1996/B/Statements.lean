/-
P0083, pages 477 and 478. Cited Theorem 1 and its derived Corollary 1.
Definitions are re-exported from B.Definitions to avoid an import cycle.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.B.Definitions
import LeanLab.Perelli1996.B.Cor1b
import LeanLab.Perelli1996.Decomp88

namespace LeanLab.Perelli1996.B

/-- Cited. P0083 Theorem 1 stays an analytic input. -/
theorem perelli_theorem1 : Theorem1 := Decomp88.theorem1

/-- Corollary 1, second part, CONDITIONAL ON the cited Theorem 1 only. -/
theorem perelli_cor1b : Cor1b := cor1b_of perelli_theorem1

end LeanLab.Perelli1996.B
