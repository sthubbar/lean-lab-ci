import LeanLab.AlmostPrimes.U1437DudekFast
import LeanLab.Verifications.U1437Fast.Chain

/-!
# Dudek 2017 with the square-free window chain, U-1437, run 20261021T1603Z-28836, I-5067

`dudek_even_fast`: every even `N ≥ 4` is a prime plus a positive square-free number, PROVED, no
cited input, with the 102 square-free windows of `Verifications/U1437Fast` in place of the 1011
Goldbach windows of `Top50/BitUpTo1e9`. `sqf_upTo_1e9`: every `N` with `3 ≤ N ≤ 10⁹`, odd or
even, PROVED. `dudek_all`: every `N > 2`, CONDITIONAL ON `DudekOddFrom (10^9)`.
AI wrote the Lean code. KNOWN mathematics. Goldbach is OPEN.
-/

namespace LeanLab.AlmostPrimes.U1437DudekAll

open LeanLab.AlmostPrimes.U1437DudekFast LeanLab.Verifications.U1437Fast

/-- Every `N` with `3 ≤ N ≤ 10⁹` is `p + (N - p)`, `p < N` prime, `N - p` square-free. PROVED. -/
theorem sqf_upTo_1e9 : SqfUpTo (10 ^ 9) := sqf_mono sqfUpTo_end (by norm_num)

/-- **Every even `N ≥ 4` is a prime plus a positive square-free number. PROVED, no cited input.** -/
theorem dudek_even_fast (N : ℕ) (hE : Even N) (h4 : 4 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m :=
  dudek_even_of_sqf sqf_upTo_1e9 N hE h4

/-- **Dudek 2017 Theorem 1, every `N > 2`, CONDITIONAL ON `DudekOddFrom (10^9)`.** -/
theorem dudek_all (hodd : DudekOddFrom (10 ^ 9)) :
    ∀ N : ℕ, 2 < N → ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) :=
  dudek_all_of_sqf sqf_upTo_1e9 hodd

end LeanLab.AlmostPrimes.U1437DudekAll

#print axioms LeanLab.AlmostPrimes.U1437DudekAll.sqf_upTo_1e9
#print axioms LeanLab.AlmostPrimes.U1437DudekAll.dudek_even_fast
#print axioms LeanLab.AlmostPrimes.U1437DudekAll.dudek_all
