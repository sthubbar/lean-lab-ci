import LeanLab.Ternary78.Paper104
import LeanLab.RamareSaouter2003.Corollary

/-
AI wrote this Lean code. Binary Goldbach is open.
P0099 printed page 13 Corollary 1, including the odd integers 3 and 5.
The existing RamareSaouter2003 proof supplies the greedy step and the upper endpoint.
This file does not recompute or prove the cited binary Goldbach verification.
-/

namespace LeanLab.Ternary78.Paper104
open LeanLab.SchnirelmannConstant

/-- CITED. P0099 page 13 Corollary 1, the exact printed odd integer range. -/
def OddPrimeRange : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → n ≤ 113256 * 10 ^ 17 → AtMostPrimes 3 n

/-- CONDITIONAL ON the main prime interval theorem and Richstein's cited
binary Goldbach verification through 4 times 10^14, P0099 reference 20.
The pre-existing endpoint certificate is proved in RamareSaouter2003.Corollary. -/
theorem oddPrimeRange_of_inputs (hI : PrimeInterval)
    (hE : LeanLab.EvenGoldbachUpTo (4 * 10 ^ 14)) : OddPrimeRange := by
  intro n hn h1 hhi
  by_cases h7 : 7 ≤ n
  · apply LeanLab.RamareSaouter2003.atMostPrimes_of_ternary_sum
    exact LeanLab.RamareSaouter2003.corollary1_of hI hE n hn h7 hhi
  · have hsmall : n = 3 ∨ n = 5 := by
      obtain ⟨k, hk⟩ := hn
      omega
    rcases hsmall with rfl | rfl
    · exact (AtMostPrimes.prime Nat.prime_three).mono (by norm_num)
    · exact (AtMostPrimes.prime Nat.prime_five).mono (by norm_num)

#print axioms oddPrimeRange_of_inputs

end LeanLab.Ternary78.Paper104
