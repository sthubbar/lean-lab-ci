/-
P0069 Baker Harman Pintz 1997, Section 5, page 53. Finite reindexing of the double
prime-factor sum j_m as a divisor sum: for each divisor n = p1 * p2 of m with
Y^c1 <= p2 < p1 < Y^c4, the inner term upperRough (m / p1 / p2) (Y^c1) depends only on
n = p1 * p2, so the double sum over prime factors reindexes as a sum over divisors.
The bound n < Y^(2 c4) uses 2 c4 = 1/2 + theta2/4 - 2 eps with
theta2 = 2(1/16 - 1/10^5). New file, no new definition.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- P0069 page 53: the exponent identity 2 * c4 = 1/2 + theta2/4 - 2 * eps, where
theta2 = 2*(1/16 - 1/10^5). PROVED by unfolding the definitions. -/
theorem upD_two_c4_eq {ε : ℝ} : 2 * upperC4 ε = 1/2 + (2*(1/16-1/10^5))/4 - 2*ε := by
  unfold upperC4
  ring

/-- P0069 page 53: the double prime-factor sum j_m reindexed as a divisor sum. For each
divisor n of m that factors as n = p1 * p2 with Y^c1 <= p2 < p1 < Y^c4, the term
upperRough (m / n) (Y^c1) appears once for each such factorization. The number of such
factorizations of n is the number of divisors d of n with d < n and Y^c1 <= d < Y^c4
and Y^c1 <= n/d < d. PROVED by finite reindexing. -/
theorem upD_j_rep (ε Y : ℝ) (m : ℕ) :
    upperJ ε Y m =
      ∑ n ∈ m.divisors,
        (((n.divisors.filter fun d : ℕ =>
            Y ^ upperC1 ε ≤ (d : ℝ) ∧ (d : ℝ) < Y ^ upperC4 ε ∧
            Y ^ upperC1 ε ≤ ((n / d : ℕ) : ℝ) ∧ ((n / d : ℕ) : ℝ) < (d : ℝ)).card : ℝ) *
          upperRough (m / n) (Y ^ upperC1 ε) := by
  unfold upperJ
  sorry

end LeanLab.BHP1997.DecompC165d
