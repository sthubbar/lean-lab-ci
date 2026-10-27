import LeanLab.Romanov.Decomp134

/-!
# Concrete instances for the conductor classification

Gallagher page 136, Lemma 9. These checks validate the twins and include a primitive character.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.Romanov.Decomp134

/-- The principal character at modulus one supplies a primitive real character instance. -/
theorem principal_one_instance :
    ∃ χ : DirichletCharacter ℂ 1, χ.IsPrimitive ∧ χ ^ 2 = 1 := by
  exact ⟨1, DirichletCharacter.isPrimitive_one_level_one, by simp⟩

/-- Small character counts and a mixed conductor rank validate the prime power corrections. -/
theorem character_count_instances :
    realCharacterCount 1 = 1 ∧ realCharacterCount 3 = 2 ∧
    realCharacterCount 4 = 2 ∧ realCharacterCount 8 = 4 ∧
    realCharacterCount 9 = 2 ∧ realCharacterRank 24 = 3 := by
  rw [realCharacterCount_eq 1 (by decide), realCharacterCount_eq 3 (by decide),
    realCharacterCount_eq 4 (by decide), realCharacterCount_eq 8 (by decide),
    realCharacterCount_eq 9 (by decide)]
  have h4 : (4 : ℕ).primeFactors = {2} := by
    exact Nat.primeFactors_prime_pow (by decide : 2 ≠ 0) Nat.prime_two
  have h8 : (8 : ℕ).primeFactors = {2} := by
    exact Nat.primeFactors_prime_pow (by decide : 3 ≠ 0) Nat.prime_two
  have h9 : (9 : ℕ).primeFactors = {3} := by
    exact Nat.primeFactors_prime_pow (by decide : 2 ≠ 0) Nat.prime_three
  have h24 : (24 : ℕ).primeFactors = {2, 3} := by
    change (3 * 8 : ℕ).primeFactors = {2, 3}
    rw [Nat.primeFactors_mul (by decide) (by decide), h8, Nat.prime_three.primeFactors]
    decide
  norm_num [realCharacterRank, h4, h8, h9, h24]

/-- Nine is a concrete bad modulus with a proper divisor of the same rank. -/
theorem bad_nine_instance :
    (¬ ∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧ (9 = r₀ ∨ 9 = 4 * r₀ ∨ 9 = 8 * r₀)) ∧
    0 < (3 : ℕ) ∧ 3 ∣ 9 ∧ 3 < 9 ∧ realCharacterRank 3 = realCharacterRank 9 := by
  refine ⟨?_, by decide, by decide, by decide, by
    have h9 : (9 : ℕ).primeFactors = {3} := Nat.primeFactors_prime_pow (by decide : 2 ≠ 0) Nat.prime_three
    norm_num [realCharacterRank, h9]⟩
  rintro ⟨m, hm, hs, heq | heq | heq⟩
  · subst m
    exact (Nat.squarefree_iff_prime_squarefree.mp hs) 3 Nat.prime_three (by decide)
  · omega
  · omega

end LeanLab.Romanov.Decomp134
