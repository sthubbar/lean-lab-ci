/-
AI wrote this Lean code for CODEX task427.
Cohen and Lenstra 1987 page 108, final trial division.
This is a scope check for the formal criterion, not a paper error.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Primality427

namespace LeanLab.DtRS1998.Scope427

/-- Cohen and Lenstra 1987 page 108, the preceding divisor congruence
condition is essential. Square modulus size, periodicity and accepted
final trials alone do not imply primality. Candidate 91 provides an
inhabited example with modulus 10 and exponent bound 1. -/
theorem trial_conditions_without_orbit :
    2 ≤ (91 : ℕ) ∧ 91 < (10 : ℕ) ^ 2 ∧ Nat.powMod 91 1 10 = 1 ∧
    (List.iterate (fun r : ℕ => r * 91 % 10) (1 % 10) 1).all
      (fun r => decide (r ∣ 91 → r = 1 ∨ r = 91)) = true ∧
    ¬ (91 : ℕ).Prime ∧
    ¬ (∀ p : ℕ, p.Prime → p ∣ 91 →
      ∃ i : ℕ, i < 1 ∧ p % 10 = 91 ^ i % 10) := by
  refine ⟨by decide, by decide, by decide, by decide, by norm_num, ?_⟩
  intro h
  obtain ⟨i, hi, heq⟩ := h 7 (by decide) (by decide)
  have hz : i = 0 := by omega
  subst i
  norm_num at heq

#print axioms trial_conditions_without_orbit

end LeanLab.DtRS1998.Scope427
