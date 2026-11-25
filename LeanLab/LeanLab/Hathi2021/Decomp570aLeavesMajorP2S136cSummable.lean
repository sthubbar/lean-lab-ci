/-
P0101 Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4.
S136 round 3 split of the HARD leaf `singularCoefficient_summable_norm` of
Decomp570aLeavesMajorP2S136Euler, page 193 definition of S of n, by the case n zero
or n nonzero. QUESTION recorded S136 round 3: the case n equal to zero is numerically
FALSE. For p odd, A of 0 and p equals minus of epsilon p plus one over p minus one squared,
epsilon the Legendre symbol of minus one mod p, checked in floating point for all p below 400,
so the norm of A of 0 and p is about 1 over p and the sum over primes diverges.
Hu uses S of n only for n nonzero, so the leaf statement over all integers r is too strong.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp570aLeavesMajorP2S136Euler

namespace LeanLab.Hathi2021.Decomp570aLeavesMajorP2S136cSummable

open Decomp570a Decomp319a

/-- LEAF: summable_norm_ne_zero, Hu page 193 display of S of n, absolute convergence for
n nonzero: A of n and p to the k vanishes for k at least two, A is multiplicative, and for
p not dividing n the Gauss sum bound for C of p, a and 2 with C of p, a and 1 equal to minus one
gives the norm of A of n and p at most a constant over p squared.
Class HARD. P0101 page 193 definition of S of n. -/
theorem summable_norm_ne_zero (r : ℤ) (hr : r ≠ 0) :
    Summable (fun q : ℕ => ‖singularCoefficient r q‖) := by
  sorry

/-- LEAF: summable_norm_zero, Hu page 193 display of S of n at n equal to zero.
Class HARD. QUESTION: believed FALSE, see the file header; numerically the norm of
A of 0 and p is about 1 over p. Not used by Hu, whose n is a positive integer.
P0101 page 193 definition of S of n. -/
theorem summable_norm_zero :
    Summable (fun q : ℕ => ‖singularCoefficient 0 q‖) := by
  sorry

/-- Assembly with the identical statement of `singularCoefficient_summable_norm`. -/
theorem singularCoefficient_summable_norm_of_leaves (r : ℤ) :
    Summable (fun q : ℕ => ‖singularCoefficient r q‖) := by
  rcases eq_or_ne r 0 with rfl | hr
  · exact summable_norm_zero
  · exact summable_norm_ne_zero r hr

end LeanLab.Hathi2021.Decomp570aLeavesMajorP2S136cSummable
