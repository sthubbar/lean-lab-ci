import LeanLab.LanguascoPerelli1996.Cor2

/-!
The original cited Corollary 2 of P0071 page 352.
CONDITIONAL ON the cited Theorem 4. No new analytic input is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996

/-- CITED. Corollary 2, from Theorem 4 with `ξ = 1/qQ`. -/
theorem corollary2 : Corollary2 := by
  exact corollary2_of_theorem4 theorem4

end LeanLab.LanguascoPerelli1996
