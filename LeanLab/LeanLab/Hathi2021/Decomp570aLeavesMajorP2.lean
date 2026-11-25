/-
P0101 Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4.
Second split, burst-20261122 S123, of the leaf `singularSeries_nonneg` of
Decomp570aLeavesMajor, page 193 definition of the singular series S of n.
The leaf is assembled as `singularSeries_nonneg_of_leaves` from the Euler product
of S of n and the nonnegativity of each local factor.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp570aLeavesMajor

namespace LeanLab.Hathi2021.Decomp570aLeavesMajorP2

open Decomp570a

/-- LEAF: Hu page 193, the Euler product of the singular series S of n for one prime
and two prime squares: the coefficient A of n and q is real, multiplicative in q,
vanishes on higher prime powers, and the series is absolutely convergent, so S of n
is the product over primes p of one plus the real part of A of n and p.
Class HARD. P0101 page 193 definition of S of n, standard Euler product. -/
theorem singularSeries_eulerProduct (r : ℤ) :
    singularSeries r = ∏' p : Nat.Primes, (1 + (singularCoefficient r (p : ℕ)).re) := by
  sorry

/-- LEAF: Hu page 193, each local factor one plus A of n and p is nonnegative, since
it is p times the normalized count of solutions modulo p of the local congruence
x plus y squared plus z squared equal to n with x, y, z prime to p.
Class MEDIUM. P0101 page 193 definition of S of n, local densities. -/
theorem localFactor_nonneg (r : ℤ) (p : Nat.Primes) :
    0 ≤ 1 + (singularCoefficient r (p : ℕ)).re := by
  sorry

/-- Hu page 193. The leaf `singularSeries_nonneg` of Decomp570aLeavesMajor, with its
exact statement, from the Euler product and the local factor bound. -/
theorem singularSeries_nonneg_of_leaves (r : ℤ) : 0 ≤ singularSeries r := by
  rw [singularSeries_eulerProduct r]
  exact tprod_nonneg fun p => localFactor_nonneg r p

end LeanLab.Hathi2021.Decomp570aLeavesMajorP2

#print axioms LeanLab.Hathi2021.Decomp570aLeavesMajorP2.singularSeries_nonneg_of_leaves
