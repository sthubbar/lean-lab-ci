/-
AI wrote this Lean code for CODEX task70.
Section 2, equations 2.1 to 2.3, pages 427 and 428.
These finite input examples test logical converses, not a Goldbach verification range.
-/
import LeanLab.SteinStein1965.Soundness

namespace LeanLab.SteinStein1965

def toyInput : List ℕ := [1, 3, 5, 9, 11]

def toyA (n : ℕ) : Bool := toyInput.contains n

/-- A basis for the input interval need not give a failure-free S-run. -/
theorem toyInput_basis : IsBasisFor toyInput 2 22 := by
  intro m hm hlo hhi
  have hc : (evensIn 2 22).all (covers toyInput) = true := by decide +kernel
  exact (covers_iff _ _).mp (List.all_eq_true.mp hc m (mem_evensIn.mpr ⟨hlo, hhi, hm⟩))

/-- A recorded failure can become covered after a later backtracking choice. -/
theorem failure_can_be_repaired :
    sAlg toyA 1 3 18 = ([1, 3, 5, 11], [18]) ∧
    covers (sAlg toyA 1 3 18).1 18 = false ∧
    sAlg toyA 1 3 20 = ([1, 3, 5, 11, 9], [18]) ∧
    covers (sAlg toyA 1 3 20).1 18 = true ∧
    covers toyInput 18 = true := by
  decide +kernel

/-- The earlier basis interval does not prevent a failure at the next target. -/
theorem basis_extension_can_fail :
    IsBasisFor (sPrime 7 14).1 14 14 ∧ (sPrime 7 16).2 = [16] := by
  constructor
  · intro m hm hlo hhi
    have he : m = 14 := by omega
    subst m
    exact ⟨7, by decide +kernel, 7, by decide +kernel, rfl⟩
  · decide +kernel

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.toyInput_basis
#print axioms LeanLab.SteinStein1965.failure_can_be_repaired
#print axioms LeanLab.SteinStein1965.basis_extension_can_fail
