import LeanLab.HelfgottMajor.ZeroCount1623
import LeanLab.HelfgottMajor.PolyaVinogradov123

/-!
HELFGOTT MAIN THEOREM burst, session CLOUD-burst20261120c, 2026-11-21. P0014, Helfgott,
Major arcs for Goldbach's problem, arXiv 1305.2897v4.

DECISION. Two of the open leaves under `Decomp123.theorem_1_1` are steps that the paper does
not prove but cites or states without proof. Each becomes a named hypothesis here, word for word
the body of the sealed leaf, so that a sorry-free conditional twin of `theorem_1_1` can take it as
an argument.
1. `PolyaVinogradov123.polya_vinogradov_4_20`, display 4.20 on page 36, an explicit
   Pólya-Vinogradov inequality that the paper states without proof or reference. Its source is
   Pomerance, Remarks on the Pólya-Vinogradov inequality, Integers 11, 2011, Theorem 1.
2. `ZeroCount1623.book_zero_count`, the explicit zero count that the paper cites on page 38 as
   display 4.26 from Rosser 1941, Theorems 17 to 19, McCurley 1984, Theorem 2.1, and Trudgian,
   Theorem 1, and that the book uses with the error of its display 16.21.
Neither hypothesis is proved here. The match theorems below only check that each body is
exactly the sealed statement; they depend on the sealed open leaf.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MainHyps123
open Real

/-- NAMED HYPOTHESIS, cited. P0014 page 36, display 4.20, stated there without proof; source
Pomerance 2011, Integers 11, Theorem 1. For a primitive character modulo q above 1 the largest
norm of a partial sum of χ is at most the three-term bound of its parity; the second case,
printed with χ(−1) = 1, is read as χ odd, as in the sealed leaf. -/
def PolyaVinogradov420 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → q ≠ 1 →
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      if χ (-1) = 1 then
        2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q
      else
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q

/-- NAMED HYPOTHESIS, cited. P0014 page 38, display 4.26, cited from Rosser 1941 Theorems 17
to 19, McCurley 1984 Theorem 2.1 and Trudgian Theorem 1, in the one-sided form of the book,
pages 431 and 432, error of display 16.21: for a primitive χ and T at least 1 the half-weighted
count of zeros with imaginary part in [0, T] is T/2π log(qT/2πe) up to 0.15 log(qT) + 3.389. -/
def BookZeroCount : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ {T : ℝ}, 1 ≤ T →
    |ZeroCount1623.bookCount χ T - ZeroCount1623.bookMain q T| ≤ ZeroCount1623.bookError q T

/-- Match check: `PolyaVinogradov420` is exactly the sealed leaf. Depends on that open leaf. -/
theorem polya_vinogradov_named_match : PolyaVinogradov420 :=
  fun _ _ χ hχ hq => PolyaVinogradov123.polya_vinogradov_4_20 χ hχ hq

/-- Match check: `BookZeroCount` is exactly the sealed leaf. Depends on that open leaf. -/
theorem book_zero_count_named_match : BookZeroCount :=
  fun _ _ χ hχ _ hT => ZeroCount1623.book_zero_count χ hχ hT

end LeanLab.HelfgottMajor.MainHyps123
