/-
Split of `KarLemma2` of `LeanLab.ExceptionalSet.KaracubaSplit`, Lemma 2 of A. A. Karacuba,
Trudy Mat. Inst. Steklov 112 (1971), p. 243-244, Vinogradov's estimate of a Weyl sum from a
rational approximation of one coefficient, Karacuba's reference [2], I. M. Vinogradov, the
method of trigonometric sums, chapter on Weyl sums.

The split is along the dependency on the mean value estimate `KarLemma1`.
`KarLemma1` as stated in the lab, Karacuba's Lemma 1, is asserted only for `n ≥ 12`, while
`KarLemma2` is asserted for every `n ≥ 1`. Vinogradov's proof of the Weyl estimate for a
polynomial with `n` as in Karacuba's Lemma 2 runs the mean value estimate in the same `n`; the
exponent `ρ = τ/(3 n² l)` and the constant `(8n)^{0.5 n l}` both depend on `n`, so the cases
`n < 12` cannot be obtained by padding the polynomial with zero coefficients to degree 12:
that only gives the weaker exponent belonging to `n = 12`.

* `leaf_karLemma2_small`: the cases `1 ≤ n ≤ 11`, LEAF, needs a mean value input in degrees
  below 12 that the stack does not state.
* `leaf_karLemma2_from_mvt`: the cases `n ≥ 12`, LEAF, conditional on `KarLemma1`, the
  Weyl shift `x ↦ x + yz`, Holder and the counting of `Σ min(U, 1/(αx+β))`, Vinogradov.
* `karLemma2_of_leaves`: PROVED from the two leaves, sorry free.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

/-- LEAF: Karacuba Lemma 2 p. 243-244 for the small degrees `1 ≤ n ≤ 11`, Vinogradov [2].
HARD. `KarLemma1` is stated only for `n ≥ 12` and does not reach these `n` with the exponent
`ρ = τ/(3 n² l)` of the Lemma, so this case needs Vinogradov's mean value estimate in degree
`n < 12`, which the lab has not stated. The statement is `KarLemma2` with `n < 12` added. -/
theorem leaf_karLemma2_small :
    ∀ n m P : ℕ, 1 ≤ n → n < 12 → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  sorry

/-- LEAF: Karacuba Lemma 2 p. 243-244 for `n ≥ 12`, from the mean value estimate Lemma 1,
by Vinogradov's proof [2]: average the sum over the shifts `x ↦ x + yz`, Taylor expand in
`yz`, apply Holder in the form of Lemma 4, bound the resulting count of solutions by Lemma 1
with `l` as in the Lemma, and use the rational approximation of `α_r` through Lemma 3.
HARD. CONDITIONAL ON `KarLemma1`. The statement is `KarLemma2` with `12 ≤ n` added. -/
theorem leaf_karLemma2_from_mvt (h1 : KarLemma1) :
    ∀ n m P : ℕ, 12 ≤ n → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  sorry

/-- PROVED from the leaves. Karacuba's Lemma 2 from the small degree case and the case
`n ≥ 12` conditional on the mean value estimate `KarLemma1`. -/
theorem karLemma2_of_leaves (h1 : KarLemma1) : KarLemma2 := by
  intro n m P hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα
  rcases lt_or_ge n 12 with h | h
  · exact leaf_karLemma2_small n m P hn h hm hP α r hr2 hr a q θ hg hq hqP hθ hα
  · exact leaf_karLemma2_from_mvt h1 n m P h hm hP α r hr2 hr a q θ hg hq hqP hθ hα

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
