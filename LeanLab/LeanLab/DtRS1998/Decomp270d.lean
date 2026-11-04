/-
AI wrote this Lean code for CODEX task270.
P0037 Theorem 2 page 206 and Sections 5.1 and 5.2 pages 211 to 214.
The twelve existing interval proofs are reused.
The remaining seventeen computational certificates are OPEN.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp121b
import LeanLab.DtRS1998.Decomp270c

namespace LeanLab.DtRS1998.Decomp270d

open Task71.Paper

/-- CONDITIONAL ON the seventeen open interval certificates.
P0037 Theorem 2 page 206, both displayed families.
This is the exact statement of Decomp121b.theorem2.
The proof does not use Decomp121b.first_family_remaining or second_family. -/
theorem theorem2 : FullTheorem2 :=
  Decomp121b.theorem2_of_remaining
    Decomp270a.first_family_remaining Decomp270c.second_family

#print axioms theorem2

end LeanLab.DtRS1998.Decomp270d
