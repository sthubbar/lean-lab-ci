/-
Split of `leaf_corollary1` of `LeanLab.GoldbachGaps.DecompJ610`, P0030 D. A. Goldston, Linnik's
theorem on Goldbach numbers in short intervals, Glasgow Math. J. 32 (1990) 285-297, Corollary 1,
display 7, page 292.

Corollary 1 says: if `J(N, K) = o(K² N)` then `Σ_{N ≤ n ≤ N + K} r(n) ~ K N / log² N`. Goldston's
proof has two parts:

* LEAF 1, the weighted count: `Σ_{N ≤ n ≤ N + K} R(n) ~ K N`, from the Theorem, display 6, by
  differencing the Fejér sum, display 7 and the lines after it.
* LEAF 2, the unweighting: `R(n) ≤ r(n) log² n`, and the pairs with a prime below
  `y = N / log³ N` number at most `2 (K + 1) y`, so the asymptotic for `R` gives the one for `r`
  with `log² N` in the denominator.

`leaf_corollary1_of_leaves` has the statement of `leaf_corollary1`, which is `Corollary1`, proved from
the two leaves alone.

AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.GoldbachGaps.Goldston1990Main

namespace LeanLab.GoldbachGaps.Feed1122Cor1
open Real Finset Filter Topology
open LeanLab.GoldbachGaps.Goldston1990

/-- LEAF: Goldston page 292, display 7 and the differencing after it: under the Theorem's range
`1 ≤ K ≤ N / log³ N` and `J(N, K) = o(K² N)`, the weighted Goldbach count over the printed
interval satisfies `Σ_{N ≤ n ≤ N + K} R(n) ~ K N`. HARD: the Fejér sum of display 6 is centred
at `N` with half width `K`, the printed interval is centred at `N + K/2` with half width `K/2`;
U-1613 suggests the trapezoid route with Cauchy's inequality and the pair sieve bound
`J(N, h) ≪ h² N`, see `DecompJ205.leaf_relabel`. -/
theorem leaf_sum_Rg_interval_asymp (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hJ : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), Rg n) / ((K N : ℝ) * N)) atTop (nhds 1) := by
  sorry

/-- LEAF: Goldston page 292, the passage from `R` to `r` in Corollary 1: for `K` in the Theorem's
range, `Σ_{N ≤ n ≤ N + K} R(n) ~ K N` implies `Σ_{N ≤ n ≤ N + K} r(n) ~ K N / log² N`. Lower half:
`R(n) ≤ r(n) log² (N + K)` and `log (N + K) ~ log N`. Upper half: a pair with both primes above
`y = N / log³ N` has weight at least `log² y`, the other pairs number at most `2 (K + 1) π(y)`,
which is `o(K N / log² N)`, and `log y ~ log N`. MEDIUM: routine bounds, the lemmas
`Rg_le_rg`, `rsumr_ge`, `rsumr_le` of `Goldston1990Cor1` do most of it. True for every `K ≥ 1`,
no growth of `K` needed. -/
theorem leaf_rg_of_Rg_interval (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hR : Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), Rg n) / ((K N : ℝ) * N)) atTop
      (nhds 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) / ((K N : ℝ) * N / Real.log N ^ 2))
      atTop (nhds 1) := by
  sorry

/-- `leaf_corollary1` of `DecompJ610`, statement identical, `Corollary1`, from the two leaves. -/
theorem leaf_corollary1_of_leaves : Corollary1 := by
  intro K hK hJ
  exact leaf_rg_of_Rg_interval K hK (leaf_sum_Rg_interval_asymp K hK hJ)

end LeanLab.GoldbachGaps.Feed1122Cor1

#print axioms LeanLab.GoldbachGaps.Feed1122Cor1.leaf_corollary1_of_leaves
