/-
Burst S82 burst-20261122 feed1122, split of `leaf_analytic_large` of `SPLIT_dudek_dunn.lean`.

Paper P0048: A. Dudek, L. Dunn, An Explicit Result for the Sum of Two Almost Primes,
arXiv 2602.22720 v4. Theorem 3.3 Case 3, N ≥ 10^200.

AI wrote this Lean code. Binary Goldbach is OPEN.

`leaf_analytic_large` asks for `TwoAlmostPrimes 40 N` at every `N ≥ 10^200`. The paper proves
this in Case 3 of Theorem 3.3 by the lower bound sieve Theorem 1.3 at `z = N^{1/20}`,
`D = z^{18.4}`, `K = 3`, with Lemma 2.1 for the dimension condition, Lemma 2.2 for `V(z)` and
Lemma 2.3 for the remainder `R₄`. That argument is already formalized, sorry free, as
`DDMain.theorem3_3_large`, CONDITIONAL ON four named inputs. One of them, `NathansonRd`, is
PROVED in `DDNathanson.nathansonRd`. The three that remain are the leaves of this file, each a
pure citation of an outside theorem:

* `leaf_rs_theorem5`: Rosser and Schoenfeld 1962 Theorem 5, in the form Lemma 2.1 Case 1 uses.
* `leaf_rs_320`: Rosser and Schoenfeld 1962 (3.20) for `z ≥ 10^10`, used by Lemmas 2.2, 2.3.
* `leaf_selberg_thm13`: Theorem 1.3 of the paper, Friedlander and Iwaniec Opera de Cribro
  Theorem 7.7, the Λ⁻Λ² lower bound sieve of dimension κ = 2 for this sequence.

`leaf_analytic_large_of_leaves` assembles the statement of `leaf_analytic_large` from them.
This file does not import `SPLIT_dudek_dunn`.
-/
import LeanLab.AlmostPrimes.DDNathanson

namespace LeanLab.AlmostPrimes.SPLIT_dudek_dunnFeed1122

open LeanLab.AlmostPrimes LeanLab.AlmostPrimes.DDMain

/-- LEAF: Rosser and Schoenfeld 1962, Theorem 5, as used in Lemma 2.1 Case 1 of P0048:
for `286 ≤ w < z`, the sum of `1/p` over primes `w ≤ p < z` is bounded by
`log(log z / log w)` plus the explicit `1/log² w` type error, in the exact form of
`DDLemma21All.RSHyp`. Class HARD as a formalization, a pure citation of an explicit prime
number theorem; the folder reduces it to `DusartThm52k2` and the finite range
`MertensRS320Link.RSHypLow`. -/
theorem leaf_rs_theorem5 : DDLemma21All.RSHyp := by
  sorry

/-- LEAF: Rosser and Schoenfeld 1962, (3.20), as used in Lemmas 2.2 and 2.3 of P0048:
`Σ_{p < z} 1/p < log log z + 0.2634` for every `z ≥ 10^10`, the form `DDMain.RSRecip`.
Class HARD as a formalization, a pure citation; the folder reduces it to `DusartThm52k2` and
`BLe` in `MertensRS320Link.RSRecip_of_dusart`. -/
theorem leaf_rs_320 : RSRecip := by
  sorry

/-- LEAF: Theorem 1.3 of P0048, which is Friedlander and Iwaniec, Opera de Cribro,
Theorem 7.7: the Λ⁻Λ² lower bound sieve of dimension κ with `s = log D / log z`,
`k = 2 + log K`, `s ≥ 2k + 3`, giving `S(A, z) ≥ X V(z) F(s, k) − 2 R₄(A, D)`, here for the
sequence `n(N − n)` of Section 2, in the form `DDMain.SelbergThm13`. Class HARD, a pure
citation of a sieve theorem not in Mathlib. -/
theorem leaf_selberg_thm13 : SelbergThm13 := by
  sorry

/-- PROVED from the leaves. The statement of `leaf_analytic_large` of `SPLIT_dudek_dunn`:
every `N ≥ 10^200` is `a + b` with `a, b > 0` and `Ω(ab) ≤ 40`. This is
`DDMain.theorem3_3_large`, P0048 Theorem 3.3 Case 3, with `NathansonRd` from
`DDNathanson.nathansonRd` and the three cited leaves above. -/
theorem leaf_analytic_large_of_leaves (N : ℕ) (hN : 2 ≤ N) (hlarge : 10 ^ 200 ≤ N) :
    TwoAlmostPrimes 40 N := by
  have hR : (10 : ℝ) ^ 200 ≤ (N : ℝ) := by exact_mod_cast hlarge
  obtain ⟨a, b, ha, hb, hab, -, h40⟩ :=
    theorem3_3_large leaf_rs_theorem5 leaf_rs_320 DDNathanson.nathansonRd leaf_selberg_thm13 N hR
  exact ⟨a, b, ha, hb, hab, h40⟩

end LeanLab.AlmostPrimes.SPLIT_dudek_dunnFeed1122
