import Mathlib

/-!
P0099, Definition 1 and Theorems 5 and 6 on p. 31.
These are cited finite-range inputs from Jaeschke, reference 11.
No finite verification or proof of either input is claimed here.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Jaeschke126

/-- Definition 1, p. 31. The odd part d of n minus one determines the
strong pseudoprime test for the integer base a. -/
def StrongPseudoprime (n : ℕ) (a : ℤ) : Prop :=
  Odd n ∧ ∃ h d : ℕ, Odd d ∧ n = 1 + 2 ^ h * d ∧
    (Int.ModEq (n : ℤ) (a ^ d) 1 ∨
      ∃ k : ℕ, k < h ∧ Int.ModEq (n : ℤ) (a ^ (2 ^ k * d)) (-1))

/-- CITED. Theorem 5, p. 31, from Jaeschke, reference 11.
The printed strict threshold is 3.4 times 10^14. -/
def theorem5_stmt : Prop := ∀ n : ℕ, Odd n → n < 340000000000000 →
    (∀ a ∈ ({2, 3, 5, 7, 11, 13, 17} : Finset ℤ), StrongPseudoprime n a) → n.Prime

/-- CITED. Theorem 6, p. 31, from Jaeschke, reference 11.
The printed strict threshold is 10^12. -/
def theorem6_stmt : Prop := ∀ n : ℕ, Odd n → n < 10 ^ 12 →
    (∀ a ∈ ({2, 13, 23, 1662803} : Finset ℤ), StrongPseudoprime n a) → n.Prime

end LeanLab.RamareSaouter2003.Jaeschke126

#print axioms LeanLab.RamareSaouter2003.Jaeschke126.StrongPseudoprime
#print axioms LeanLab.RamareSaouter2003.Jaeschke126.theorem5_stmt
#print axioms LeanLab.RamareSaouter2003.Jaeschke126.theorem6_stmt
