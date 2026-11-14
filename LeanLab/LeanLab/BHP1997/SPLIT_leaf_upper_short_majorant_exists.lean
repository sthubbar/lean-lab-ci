/-
Split of `leaf_upper_short_majorant_exists` of `SPLIT_upper_short_coefficient`.

The sealed step asks for one family `b1` carrying three properties: the divisor bound at exponent
`B`, the short-interval character distribution clause at the short-weight density, and eventual
majorisation of the two positive pieces `upperG + upperJ` on every short interval. The split below
keeps the family fixed at the masked two-positive-piece family
`fun x m => if m ∈ rightInterval ε x then upperG … m + upperJ … m else 0`, so that the majorisation
is the reflexivity of `≤` and disappears from the leaf list, and the two remaining properties become
leaf 1 and leaf 2. The masked family is the two positive pieces themselves, so nothing is weakened
and nothing is added: leaf 1 is exactly the divisor-bound conjunct of the sealed step and leaf 2 is
exactly its distribution conjunct, and the reassembly is logic plus `if_pos`.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_upper_short_coefficient

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF 1 of 2. Step: the divisor bound for the masked two-positive-piece family. For a divisor
exponent `B` with `0 ≤ B` and a cutoff `eps` at most one over ten to the eighth, there is a constant
`C` with `|b1 x k| ≤ C * (number of divisors of k) ^ B` for every real `x` and every natural `k`,
where `b1 x m` is `upperG eps (x ^ (11 / 20 + eps)) m + upperJ eps (x ^ (11 / 20 + eps)) m` when
`m` lies in the short interval `rightInterval eps x` and `0` otherwise.

This is one estimate and it mentions neither the character distribution clause nor any character
sum. Only `m` in the short interval is tested, and there `m ≤ 2 * (x ^ (11 / 20 + eps))`; every
prime counted by the two positive pieces is at least `Y ^ c1` with `c1 ≥ 1 / 9`, so at most `18`
distinct such primes divide `m`, which bounds `upperG` by `1` and `upperJ` by `18 * 18`. Edge cases
tested before keeping the leaf: at `k = 0` the interval `rightInterval eps x` has no member (it
starts above `⌊x ^ (11 / 20 + eps)⌋ ≥ 0`) so the left side is `0` and `(Nat.divisors 0).card = 0`
makes the right side `C * 0 ^ B = 0`; at `k = 1` both pieces are `1` and `0` because `1` has no
prime factors, and `(Nat.divisors 1).card = 1` with `1 ^ B = 1`; for negative `x`, or `x` with
`x ^ (11 / 20 + eps) < 1`, the interval is empty or a singleton and the bound is still met; `B = 0`
is the strongest case and is covered by `C` alone. -/
theorem leaf_upper_short_majorant_divisor_bound (ε B : ℝ) (hB : 0 ≤ B)
    (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ C : ℝ, ∀ x k,
      |(if k ∈ rightInterval ε x then
        upperG ε (x ^ (11 / 20 + ε)) k + upperJ ε (x ^ (11 / 20 + ε)) k else 0)|
        ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by
  sorry

/-- LEAF 2 of 2. Step: the short-interval character distribution clause for the same masked
two-positive-piece family, at the short-weight density `ω (1 / c4) / c4 + upperDeletedIntegral ω ε`
with `c4 = 1 / 4 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 8 - ε`. For every logarithmic saving `A` there is
`C` such that for `x ≥ C`, every modulus `q` with `1 ≤ q ≤ (Real.log x) ^ A`, every character `χ`
modulo `q` and every `t ≤ 2 * x ^ (11 / 20 + eps)`, the centred character sum over the short
interval truncated at `t` is at most `C * x ^ (11 / 20 + eps) * (Real.log x) ^ (-A)`.

This is one bound and it carries no divisor exponent and no majorisation of any other family, so it
is strictly easier than the sealed step. Only terms with `m` in the short interval are summed, so
masking the family outside the interval changes nothing. Edge cases tested: `t` may be negative, in
which case the filtered sum has no term and the left side is the norm of `0 - delta χ * v / log`,
which is `0` when `delta χ = 0`; `q = 1` gives the principal character and a single term per `m`;
`x` small is excluded by `C ≤ x`; the density may be negative when `upperDeletedIntegral ω ε` is
negative, and the clause is an upper bound so it remains satisfiable. -/
theorem leaf_upper_short_majorant_distribution
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε)
      (fun x m => if m ∈ rightInterval ε x then
        upperG ε (x ^ (11 / 20 + ε)) m + upperJ ε (x ^ (11 / 20 + ε)) m else 0) := by
  sorry

/-- The sealed step, assembled from the two leaves with no sorry and without using
`leaf_upper_short_majorant_exists`. Take `b1` to be the masked two-positive-piece family; its
divisor bound is leaf 1, its distribution clause is leaf 2, and the majorisation holds with `X = 0`
because for `x ≥ 0` and `m` in `rightInterval ε x` the mask is positive and both sides are the same
real number. -/
theorem leaf_upper_short_majorant_exists_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ b1 : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        upperG ε (x ^ (11 / 20 + ε)) m + upperJ ε (x ^ (11 / 20 + ε)) m ≤ b1 x m := by
  refine ⟨fun x m => if m ∈ rightInterval ε x then
      upperG ε (x ^ (11 / 20 + ε)) m + upperJ ε (x ^ (11 / 20 + ε)) m else 0,
    leaf_upper_short_majorant_divisor_bound ε B hB hε8,
    leaf_upper_short_majorant_distribution h4 h9 hω hz hB hε hε8, 0, ?_⟩
  intro x hx m hm
  exact le_of_eq (ite_eq_left hm).symm
