import LeanLab.ChirreHagen2025.Decomp429e
import LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2

/-!
Split of `Decomp429e.mangoldt_psi_transfer`, burst-20261122, session S88.
Ramare 2013 pages 118 to 120 and JRT 2023 page 3 proof of Lemma 9.
The weighted Mangoldt sum is written by partial summation as
log x - gamma + (psi x - x)/x minus a tail integral of (psi t - t)/t^2,
and the tail integral is bounded by the explicit formula.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp429eSplitTransfer
open ArithmeticFunction LeanLab.ChirreHagen2025.Decomp429e

/-- Formerly LEAF: JRT 2023 page 3 proof of Lemma 9 and Ramare 2013 page 118, the exact
partial summation identity for the weighted Mangoldt sum, using
1 + gamma + integral over [1, infinity) of (psi t - t)/t^2 = 0. Class HARD.
The improper integral is the Bochner integral over Ioi x; the integrand is
integrable there by the prime number theorem with error term. PROVED S132 from
`Decomp429eSplitTransferP2.mangoldt_partial_summation_identity_of_leaves`, whose LEAFs are all
proved; the import direction between the two files was reversed for this. -/
theorem mangoldt_partial_summation_identity (x : ℝ) (hx : 100000 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      Real.log x - Real.eulerMascheroniConstant + (Chebyshev.psi x - x) / x -
        ∫ t in Set.Ioi x, (Chebyshev.psi t - t) / t ^ 2 :=
  LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2.mangoldt_partial_summation_identity_of_leaves x hx

/-- LEAF: Ramare 2013 pages 118 to 120, equation 5.1 and the estimates after it,
the explicit formula bound for the tail integral: the low verified zeros give
0.047/sqrt x, the constant term log 2 pi gives log(2 pi)/x up to 0.0001/x from the
trivial zeros, and the remaining zeros give zeroTailError x. Class HARD. -/
theorem tail_integral_explicit_bound (x : ℝ) (hx : 100000 ≤ x) :
    -(∫ t in Set.Ioi x, (Chebyshev.psi t - t) / t ^ 2) ≤
      0.047 / Real.sqrt x + (Real.log (2 * Real.pi) + 0.0001) / x +
        zeroTailError x := by
  sorry

/-- Exact parent statement `Decomp429e.mangoldt_psi_transfer`.
CONDITIONAL ON the LEAF `tail_integral_explicit_bound` above. -/
theorem mangoldt_psi_transfer_of_leaves (x : ℝ) (hx : 100000 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) - Real.log x +
        Real.eulerMascheroniConstant ≤
      |Chebyshev.psi x - x| / x + 0.047 / Real.sqrt x +
        (Real.log (2 * Real.pi) + 0.0001) / x + zeroTailError x := by
  have hx0 : 0 < x := by linarith
  have h1 := mangoldt_partial_summation_identity x hx
  have h2 := tail_integral_explicit_bound x hx
  have h3 : (Chebyshev.psi x - x) / x ≤ |Chebyshev.psi x - x| / x :=
    div_le_div_of_nonneg_right (le_abs_self _) hx0.le
  rw [h1]
  linarith

end LeanLab.ChirreHagen2025.Decomp429eSplitTransfer
#print axioms LeanLab.ChirreHagen2025.Decomp429eSplitTransfer.mangoldt_partial_summation_identity
