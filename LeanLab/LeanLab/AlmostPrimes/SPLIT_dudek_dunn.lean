/-
Split of the statement `dudek_dunn` of `LeanLab.AlmostPrimes.Statements`:
`∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N`.

The single conclusion is cut into five range-restricted leaves, following the way the range of
`N` is handled in the surrounding folder:

* below `2^40 + 1` the degenerate sum `N = 1 + (N - 1)` suffices, because a number of size at
  most `2^40` has at most `40` prime factors counted with multiplicity;
* from `2^40 + 1` up to `4 * 10 ^ 18`, split by the parity of `N`;
* in the window `4 * 10 ^ 18 < N < 10 ^ 200`, the finite verification of the sieve;
* from `10 ^ 200` up, the analytic lower bound for the sieve at `N ^ (1/20)`.

`dudek_dunn_split` is assembled from the five leaves with no `sorry`. The leaves themselves are
left open.
-/
import LeanLab.AlmostPrimes.Statements

namespace LeanLab.AlmostPrimes

/-! ### Helpers -/

/-- The factors of `n ≠ 0` are primes, hence at least `2`, so their product is at least `2`
to the power of their count: `2 ^ Ω n ≤ n`. -/
private theorem two_pow_bigOmega_le {m : ℕ} (hm : m ≠ 0) : 2 ^ bigOmega m ≤ m := by
  have h := List.pow_length_le_prod (m.primeFactorsList) 2
    fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
  rw [Nat.prod_primeFactorsList hm] at h
  simpa [bigOmega] using h

/-- `Ω m ≤ k` for `m ≤ 2 ^ k`: a number of size at most `2 ^ k` has at most `k` prime factors
counted with multiplicity. -/
private theorem bigOmega_le_of_le_pow_two {m k : ℕ} (hm : m ≤ 2 ^ k) : bigOmega m ≤ k := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    simp [bigOmega]
  · have h := two_pow_bigOmega_le hpos.ne'
    exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp (le_trans h hm)

/-! ### Leaves -/

/-- LEAF: the bottom of the range, the step that takes the summand `a = 1`. For `2 ≤ N ≤ 2^40 + 1`
the split `N = 1 + (N - 1)` has `N - 1 ≤ 2^40`, and `Ω(N - 1) ≤ 40` because a product of
`Ω(m)` primes is at least `2 ^ Ω(m)`. -/
theorem leaf_one_plus_small (N : ℕ) (hN : 2 ≤ N) (hsmall : N ≤ 2 ^ 40 + 1) :
    TwoAlmostPrimes 40 N := by
  have hpos : 0 < N - 1 := by omega
  refine ⟨1, N - 1, Nat.one_pos, hpos, by omega, ?_⟩
  rw [Nat.one_mul]
  exact bigOmega_le_of_le_pow_two (by omega)

/-- LEAF: the even half of the finite range above `2^40 + 1` and up to `4 * 10 ^ 18`. This is the
part of the range covered by the prime gap table together with the finite sieve check. -/
theorem leaf_even_finite (N : ℕ) (hN : 2 ≤ N) (hEven : Even N) (hlow : 2 ^ 40 + 1 < N)
    (hhigh : N ≤ 4 * 10 ^ 18) : TwoAlmostPrimes 40 N := by
  sorry

/-- LEAF: the odd half of the finite range above `2^40 + 1` and up to `4 * 10 ^ 18`, the same
finite verification as the even half, on the odd `N`. -/
theorem leaf_odd_finite (N : ℕ) (hN : 2 ≤ N) (hOdd : Odd N) (hlow : 2 ^ 40 + 1 < N)
    (hhigh : N ≤ 4 * 10 ^ 18) : TwoAlmostPrimes 40 N := by
  sorry

/-- LEAF: the window `4 * 10 ^ 18 < N < 10 ^ 200`, where the sieve `S(A, N ^ (1/20))` is
positive by the finite verification of the surrounding development. -/
theorem leaf_finite_window (N : ℕ) (hN : 2 ≤ N) (hlow : 4 * 10 ^ 18 < N)
    (hhigh : N < 10 ^ 200) : TwoAlmostPrimes 40 N := by
  sorry

/-- LEAF: the analytic range `10 ^ 200 ≤ N`, where the lower bound sieve at `N ^ (1/20)` makes
`S(A, N ^ (1/20))` positive without any finite check, and the counting step converts one element
of the sifted set into the pair `a + b` with `Ω(ab) ≤ 40`. -/
theorem leaf_analytic_large (N : ℕ) (hN : 2 ≤ N) (hlarge : 10 ^ 200 ≤ N) :
    TwoAlmostPrimes 40 N := by
  sorry

/-! ### Assembly -/

/-- `dudek_dunn` from the five range leaves. -/
theorem dudek_dunn_split : ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N := by
  intro N hN
  by_cases h1 : N ≤ 2 ^ 40 + 1
  · exact leaf_one_plus_small N hN h1
  · have h1' : 2 ^ 40 + 1 < N := lt_of_not_ge h1
    by_cases h2 : N ≤ 4 * 10 ^ 18
    · rcases Nat.even_or_odd N with hEven | hOdd
      · exact leaf_even_finite N hN hEven h1' h2
      · exact leaf_odd_finite N hN hOdd h1' h2
    · have h2' : 4 * 10 ^ 18 < N := lt_of_not_ge h2
      by_cases h3 : N < 10 ^ 200
      · exact leaf_finite_window N hN h2' h3
      · exact leaf_analytic_large N hN (le_of_not_gt h3)

end LeanLab.AlmostPrimes
