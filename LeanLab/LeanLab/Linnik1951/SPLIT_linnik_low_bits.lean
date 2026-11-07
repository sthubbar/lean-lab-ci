import LeanLab.Linnik1951.Novelty1620

/-!
# Split of `linnik_low_bits`, `Linnik1951/Novelty1620`

`linnik_low_bits` states: under GRH, for every real `θ` with `1 / 2 < θ < 1` there is `k₀` such
that every sufficiently large even `N` is a sum of two primes and exactly `k` powers of two, each
power at most `N ^ θ`, for every `k ≥ k₀`.

The split goes through a single power count `K`.

* `leaf_grh_powers_within_window`, the analytic input: one count `K` and one threshold such that
  every large even `N` is two primes plus at most `K` powers of two of size at most `N ^ θ`, and
  those powers sum to at least `2 * K`.
* `leaf_split_at_most_to_exact`, the binary splitting estimate: a sum of at most `K` powers of two
  that is at least `2 * K` is also a sum of exactly `K` powers of two, none of them larger.
* `leaf_rep_add_one_power`, one step up in the count at the cost of shifting `N` by two: a
  representation of `N - 2` with `k` powers gives one of `N` with `k + 1` powers.
* `leaf_rpow_ge_two`, the numeric side condition of that step: `2 ≤ N ^ θ` for `N ≥ 4`.

Assembly: the analytic leaf supplies `k = K` for all large even `N`, the splitting leaf turns
"at most" into "exactly", and the step leaf raises the count one at a time, so every `k ≥ K` is
covered. This file proves nothing about the four leaves, which stay open.
-/

namespace LeanLab.Linnik1951.Novelty1620

open LeanLab.Linnik LeanLab.DERZ1997

/-- LEAF. Step 1 of the split, the analytic input. Assume GRH. For every real `θ` with
`1 / 2 < θ < 1` there are `K` and `N₀` such that every even `N > N₀` is a sum of two primes and
at most `K` powers of two `2 ^ ν i` with `1 ≤ ν i` and `2 ^ ν i ≤ N ^ θ`, and the powers sum to at
least `2 * K`. The count `K` is one fixed number, not yet the exact count `k` of the target. -/
theorem leaf_grh_powers_within_window (hG : GRH) :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      ∃ K N₀ : ℕ, ∀ N : ℕ, Even N → N₀ < N →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
          ∃ t : ℕ, t ≤ K ∧ ∃ ν : Fin t → ℕ,
            (∀ i, 1 ≤ ν i ∧ (2 : ℝ) ^ (ν i) ≤ (N : ℝ) ^ θ) ∧
              N = p + q + ∑ i, 2 ^ (ν i) ∧ 2 * K ≤ ∑ i, 2 ^ (ν i) := by
  sorry

/-- LEAF. Step 2 of the split, the binary splitting estimate. Let `0 ≤ X`, let `M` be a sum of
`t ≤ K` powers of two `2 ^ ν i` with `1 ≤ ν i` and `2 ^ ν i ≤ X`, and let `2 * K ≤ M`. Then `M` is
also a sum of exactly `K` powers of two with `1 ≤ ν' i` and `2 ^ ν' i ≤ X`. Splitting `2 ^ e` with
`2 ≤ e` into `2 ^ (e - 1) + 2 ^ (e - 1)` raises the count by one and lowers no single power, so
every count from `t` up to `M / 2` is reached, and `2 * K ≤ M` puts `K` in that range. -/
theorem leaf_split_at_most_to_exact {K M : ℕ} {X : ℝ} (hX : 0 ≤ X)
    (hK : 2 * K ≤ M) (t : ℕ) (ht : t ≤ K) (ν : Fin t → ℕ)
    (hν : ∀ i, 1 ≤ ν i ∧ (2 : ℝ) ^ (ν i) ≤ X)
    (hM : M = ∑ i, 2 ^ (ν i)) :
    ∃ ν' : Fin K → ℕ, (∀ i, 1 ≤ ν' i ∧ (2 : ℝ) ^ (ν' i) ≤ X) ∧ M = ∑ i, 2 ^ (ν' i) := by
  sorry

/-- LEAF. Step 3 of the split, one step in the count. For `1 / 2 ≤ θ` and `4 ≤ N`, a
representation of `N - 2` as two primes plus `k` powers of two, each at most `(N - 2) ^ θ`, gives a
representation of `N` as two primes plus `k + 1` powers of two each at most `N ^ θ`: append the
power `2 ^ 1 = 2`, and `(N - 2) ^ θ ≤ N ^ θ` because `θ ≥ 0`. -/
theorem leaf_rep_add_one_power {θ : ℝ} (hθ : 1 / 2 ≤ θ) {k N : ℕ} (hN : 4 ≤ N)
    (h : LowBitsRep θ k (N - 2)) : LowBitsRep θ (k + 1) N := by
  sorry

/-- LEAF. Step 4 of the split, the numeric side condition of step 3 and nothing more:
`2 ≤ N ^ θ` for every `N ≥ 4` and every `θ ≥ 1 / 2`, since `2 = 4 ^ (1 / 2) ≤ 4 ^ θ ≤ N ^ θ`. -/
theorem leaf_rpow_ge_two {θ : ℝ} (hθ : 1 / 2 ≤ θ) {N : ℕ} (hN : 4 ≤ N) :
    (2 : ℝ) ≤ (N : ℝ) ^ θ := by
  sorry

/-- `linnik_low_bits` of `Novelty1620`, assembled from the four leaves above: the analytic leaf
gives the count `K` for all large even `N`, the splitting leaf makes the count exact, and the
count-raising leaf covers every `k ≥ K`. -/
theorem linnik_low_bits_split (_hG : GRH) :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → AllLargeEven (LowBitsRep θ k) := by
  intro θ hθ1 hθ2
  obtain ⟨K, N₀, hN₀⟩ := leaf_grh_powers_within_window _hG θ hθ1 hθ2
  have hθhalf : 1 / 2 ≤ θ := le_of_lt hθ1
  have base : AllLargeEven (LowBitsRep θ K) := by
    refine ⟨N₀, ?_⟩
    intro N hEven hN
    obtain ⟨p, q, hp, hq, t, ht, ν, hν, hNsum, hKle⟩ := hN₀ N hEven hN
    obtain ⟨ν', hν', hsum⟩ :=
      leaf_split_at_most_to_exact (K := K) (M := ∑ i, 2 ^ (ν i)) (X := (N : ℝ) ^ θ)
        (Real.rpow_nonneg (Nat.cast_nonneg N) θ) hKle t ht ν hν rfl
    exact ⟨p, q, hp, hq, ν', hν', by rw [hNsum, hsum]⟩
  have step : ∀ k : ℕ, K ≤ k → AllLargeEven (LowBitsRep θ k) →
      AllLargeEven (LowBitsRep θ (k + 1)) := by
    intro k _ hAle
    obtain ⟨M₀, hM₀⟩ := hAle
    refine ⟨M₀ + 6, ?_⟩
    intro N hEven hN
    obtain ⟨m, hm⟩ := hEven
    have hN8 : 8 ≤ N := by omega
    have hEven' : Even (N - 2) := ⟨m - 1, by omega⟩
    have hlt : M₀ < N - 2 := by omega
    exact leaf_rep_add_one_power hθhalf (by omega : 4 ≤ N) (hM₀ (N - 2) hEven' hlt)
  refine ⟨K, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base
  | succ n hn ih => exact step n hn ih

end LeanLab.Linnik1951.Novelty1620

#print axioms LeanLab.Linnik1951.Novelty1620.linnik_low_bits_split
