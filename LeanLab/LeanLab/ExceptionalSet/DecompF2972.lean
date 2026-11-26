/-
Split of `lemma10` from `LeanLab.ExceptionalSet.State1539` for FREE-nv-nemotron task2972.

The target is the exponential sum estimate in `Lemma10`. Its proof has two analytic routes.
The main route uses the Vinogradov mean value estimate for the large derivative order case and
the Vinogradov Weyl sum estimate for the small derivative order case. A separate first
derivative route handles the one derivative set `{1}` that the main route does not cover.

The file has five leaves. The first two are the two analytic mean value estimates. The third
is the bound on the auxiliary double sum in the large order case. The fourth is the small
order case. The fifth is the first derivative case. The assembly below combines the large
and small cases into the derivative order theorem, then translates that theorem into the
target class. The assembly contains no admission of its own.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.F2972

open Real Finset Filter
open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.U1539.KaracubaSplit

/-- LEAF. Mean value estimate for the large derivative order case. For every degree `n` at
least twelve, every positive integer `l`, and every admissible even moment `b`, the mean
value of the `2b`th power of a complete degree `n` Weyl sum is at most the displayed
constant times `P` to the exponent recorded in `KarLemma1`. This is the one mean value
estimate used by the large order argument. -/
theorem leaf_F2972_vinogradov_mean_value : KarLemma1 := by
  sorry

/-- LEAF. Rational approximation estimate for the small derivative order case. For a
polynomial of degree at most `n+1`, a nonzero integer frequency, a reduced rational
approximation `a/q` with `1 < q < P^r`, and a suitable coefficient of order `r` between two
and `n+1`, the Weyl sum is at most the factor in `KarLemma2`. This is the one Weyl sum
estimate used by the small order argument. -/
theorem leaf_F2972_vinogradov_weyl_estimate : KarLemma2 := by
  sorry

/-- LEAF. Auxiliary double sum estimate for the large derivative order case. With the five
positive constants satisfying the displayed restrictions, the auxiliary sum `W(a)` over the
two block indices is at most `A (P2+1)^2 P^(-gamma/n^2)` whenever the block lies in the
interval covered by the derivative hypotheses. The estimate is `KarWBound` with the same
parameters. -/
theorem leaf_F2972_large_order_W_bound :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 → KarWBound c0 c1 c2 c3 c4 := by
  sorry

/-- LEAF. Small derivative order case. With the five positive constants satisfying the
displayed restrictions and with `n` below the threshold `karN0 c1 c2 c4`, every function in
the derivative hypotheses has the exponential sum bound in `KarCase` with that small order
predicate. This is the rational approximation route through the Weyl sum estimate. -/
theorem leaf_F2972_small_order_case :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      KarCase c0 c1 c2 c3 (fun n => (n : ℝ) < karN0 c1 c2 c4) := by
  sorry

/-- LEAF. First derivative case. If the derivative set is exactly `{1}`, then the parameter
condition forces `delta k ≤ 1`. Under the differentiability, top derivative, and first
derivative bounds, the exponential sum is at most `B N^(1-c/k^2)`. This is the separate
first derivative route and is narrower than the target class. -/
theorem leaf_F2972_singleton_order_case : LeafS1Case := by
  sorry

/-- Assembly of the split. The large and small derivative order leaves give the general
derivative order theorem. The first derivative leaf handles the set `{1}`. The notation
bridge then gives exactly the target estimate. -/
theorem lemma10_F2972 : Lemma10 := by
  have hlarge : ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      KarCase c0 c1 c2 c3 (fun n => karN0 c1 c2 c4 ≤ n) := by
    intro c0 c1 c2 c3 c4 h0 h1 h2 h3 h4 h01 h11 h241
    exact largeCase_of_W (by linarith)
      (leaf_F2972_large_order_W_bound c0 c1 c2 c3 c4 h0 h1 h2 h3 h4 h01 h11 h241)
  have hsmall : ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      KarCase c0 c1 c2 c3 (fun n => (n : ℝ) < karN0 c1 c2 c4) :=
    leaf_F2972_small_order_case
  exact lemma10_of_thm1 (karacubaTheorem1_of_cases hlarge hsmall)
    leaf_F2972_singleton_order_case

end LeanLab.ExceptionalSet.U1539.F2972

#print axioms LeanLab.ExceptionalSet.U1539.F2972.lemma10_F2972
