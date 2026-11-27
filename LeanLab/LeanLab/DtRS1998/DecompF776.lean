/-
Split of the sealed statement finite_goldbach_2e13_to_4e13 of
LeanLab.DtRS1998.SPLIT_cray_middle1_blocks.
The range [2*10^13, 4*10^13] is cut into four consecutive windows of width
5*10^12 each. Each window is a finite certificate request on its own.
The assembly is a case split on the window holding N; it adds no input.
AI wrote this Lean code. Binary Goldbach is open.
-/

import LeanLab.DtRS1998.SPLIT_cray_middle1_blocks

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- LEAF. First window: every even N in [2*10^13, 25*10^12] is a sum of two
primes. This is a finite instance of the binary Goldbach conjecture for this
sub-range; the certificate is open. -/
theorem finite_goldbach_2e13_to_25e12 (N : ℕ) (hlo : 2 * 10 ^ 13 ≤ N)
    (hhi : N ≤ 25 * 10 ^ 12) (he : Even N) :
    ∃ p : ℕ, p.Prime ∧ p ≤ N ∧ (N - p).Prime := by
  rcases Theorem1.theorem1_upTo_of_P0005 (N := N) he (by omega) (by omega) with
    ⟨p, q, hp, hq, hsum⟩
  exact ⟨p, hp, by omega, by omega⟩

/-- LEAF. Second window: every even N in [25*10^12, 3*10^13] is a sum of two
primes. Finite instance of binary Goldbach for this sub-range; open. -/
theorem finite_goldbach_25e12_to_3e13 (N : ℕ) (hlo : 25 * 10 ^ 12 ≤ N)
    (hhi : N ≤ 3 * 10 ^ 13) (he : Even N) :
    ∃ p : ℕ, p.Prime ∧ p ≤ N ∧ (N - p).Prime := by
  sorry

/-- LEAF. Third window: every even N in [3*10^13, 35*10^12] is a sum of two
primes. Finite instance of binary Goldbach for this sub-range; open. -/
theorem finite_goldbach_3e13_to_35e12 (N : ℕ) (hlo : 3 * 10 ^ 13 ≤ N)
    (hhi : N ≤ 35 * 10 ^ 12) (he : Even N) :
    ∃ p : ℕ, p.Prime ∧ p ≤ N ∧ (N - p).Prime := by
  sorry

/-- LEAF. Fourth window: every even N in [35*10^12, 4*10^13] is a sum of two
primes. Finite instance of binary Goldbach for this sub-range; open. -/
theorem finite_goldbach_35e12_to_4e13 (N : ℕ) (hlo : 35 * 10 ^ 12 ≤ N)
    (hhi : N ≤ 4 * 10 ^ 13) (he : Even N) :
    ∃ p : ℕ, p.Prime ∧ p ≤ N ∧ (N - p).Prime := by
  sorry

/-- The sealed statement of finite_goldbach_2e13_to_4e13, assembled from the
four window leaves by a case split on the window that holds N. -/
theorem finite_goldbach_2e13_to_4e13_F776 (N : ℕ) (hlo : 2 * 10 ^ 13 ≤ N)
    (hhi : N ≤ 4 * 10 ^ 13) (he : Even N) :
    ∃ p : ℕ, p.Prime ∧ p ≤ N ∧ (N - p).Prime := by
  by_cases h1 : N ≤ 25 * 10 ^ 12
  · exact finite_goldbach_2e13_to_25e12 N hlo h1 he
  · have h1g : 25 * 10 ^ 12 ≤ N := by omega
    by_cases h2 : N ≤ 3 * 10 ^ 13
    · exact finite_goldbach_25e12_to_3e13 N h1g h2 he
    · have h2g : 3 * 10 ^ 13 ≤ N := by omega
      by_cases h3 : N ≤ 35 * 10 ^ 12
      · exact finite_goldbach_3e13_to_35e12 N h2g h3 he
      · have h3g : 35 * 10 ^ 12 ≤ N := by omega
        exact finite_goldbach_35e12_to_4e13 N h3g hhi he

#print axioms finite_goldbach_2e13_to_4e13_F776

end LeanLab.DtRS1998.Decomp270e
