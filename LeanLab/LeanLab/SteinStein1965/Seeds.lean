/-
AI wrote this Lean code for CODEX task70.
Section 3, page 428, starts the prime input at p0 and the next odd prime.
Bertrand's postulate validates the finite search already used by nextA.
-/
import LeanLab.SteinStein1965.Soundness
import Mathlib.NumberTheory.Bertrand

namespace LeanLab.SteinStein1965

theorem nextA_prime (p0 : ℕ) (hpos : 1 ≤ p0) : (nextA p0).Prime := by
  by_cases hone : p0 = 1
  · subst p0
    decide +kernel
  · have htwo : 2 ≤ p0 := by omega
    obtain ⟨q, hq, hpq, hqbound⟩ := Nat.exists_prime_lt_and_le_two_mul p0 (by omega)
    have hqmem : q ∈ List.range' (p0 + 1) (p0 + 3) := by
      rw [List.mem_range'_1]
      omega
    have hqtest : (q != 2 && primeB q) = true := by
      simp [primeB_complete hq, show q ≠ 2 by omega]
    unfold nextA
    cases he : (List.range' (p0 + 1) (p0 + 3)).find? (fun n => n != 2 && primeB n) with
    | none =>
      have hn := List.find?_eq_none.mp he q hqmem
      exact False.elim (hn hqtest)
    | some a =>
      have ha := List.find?_some he
      simp only [Bool.and_eq_true] at ha
      exact primeB_sound ha.2

theorem nextA_odd (p0 : ℕ) (hpos : 1 ≤ p0) : Odd (nextA p0) := by
  have hp := nextA_prime p0 hpos
  have hgt := nextA_gt p0 hp
  have hn : nextA p0 ≠ 2 := by
    by_cases hone : p0 = 1
    · subst p0
      decide
    · omega
  exact hp.odd_of_ne_two hn

/-- Remove the auxiliary primality assumption on the computed second seed. -/
theorem sPrime_elems_prime_unconditional (p0 N b : ℕ) (hp0 : p0.Prime)
    (hb : b ∈ (sPrime p0 N).1) : b.Prime ∧ p0 ≤ b :=
  sPrime_elems_prime p0 N b hp0 (nextA_prime p0 (by have := hp0.two_le; omega)) hb

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.nextA_prime
#print axioms LeanLab.SteinStein1965.nextA_odd
#print axioms LeanLab.SteinStein1965.sPrime_elems_prime_unconditional
