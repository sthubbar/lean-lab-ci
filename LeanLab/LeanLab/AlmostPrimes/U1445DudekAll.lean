import LeanLab.AlmostPrimes.U1445DudekAllOdd
import LeanLab.AlmostPrimes.U1437DudekAll

/-!
# Dudek 2017 Theorem 1, final assembly, U-1445, run 20261021T2003Z-599

AI wrote the Lean code. KNOWN mathematics, Dudek 2017 Theorem 1, arXiv 1410.7459. Goldbach is OPEN.
Imports the square-free window chain through `U1437DudekAll.sqf_upTo_1e9`, PROVED.

* `dudek_all_odd`: every odd `N ≥ 3` is `p + m`, `p` prime, `m ≥ 1` square-free, CONDITIONAL ON
  `BMORCor16`.
* `dudek_all_bmor`: every `N > 2`, CONDITIONAL ON `BMORCor16`.
-/

namespace LeanLab.AlmostPrimes.U1445DudekAll

open LeanLab.AlmostPrimes.U1445DudekOdd LeanLab.AlmostPrimes.U1445DudekAllOdd

/-- **Dudek 2017 Theorem 1, every `N > 2`, CONDITIONAL ON `BMORCor16`.** -/
theorem dudek_all_bmor (hB : BMORCor16) :
    ∀ N : ℕ, 2 < N → ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) :=
  LeanLab.AlmostPrimes.U1437DudekAll.dudek_all (dudekOddFrom_1e9 hB)

/-- **The odd half: every odd `N ≥ 3` is a prime plus a positive square-free number,
CONDITIONAL ON `BMORCor16`.** -/
theorem dudek_all_odd (hB : BMORCor16) (N : ℕ) (hO : Odd N) (h3 : 3 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  rw [← LeanLab.AlmostPrimes.U1437DudekFast.dudekAt_iff]
  have := hO
  exact dudek_all_bmor hB N (by omega)

end LeanLab.AlmostPrimes.U1445DudekAll

#print axioms LeanLab.AlmostPrimes.U1445DudekAll.dudek_all_bmor
#print axioms LeanLab.AlmostPrimes.U1445DudekAll.dudek_all_odd
