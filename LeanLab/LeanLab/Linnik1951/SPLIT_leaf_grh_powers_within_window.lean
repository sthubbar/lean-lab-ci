import LeanLab.Linnik1951.SPLIT_linnik_low_bits

/-!
# Split of `leaf_grh_powers_within_window`, `Linnik1951/SPLIT_linnik_low_bits`

`leaf_grh_powers_within_window` is the analytic input of the `linnik_low_bits` split: under GRH, for
every real `θ` with `1 / 2 < θ < 1` there are `K` and `N₀` such that every even `N > N₀` is a sum of
two primes and at most `K` powers of two, each power at most `N ^ θ` and the powers summing to at
least `2 * K`.

The split cuts that statement into three steps, each strictly smaller than the whole.

* `leaf_grh_even_goldbach`, the analytic input with no powers of two in it at all: under GRH some
  threshold `M₀` has every even `m > M₀` equal to a sum of two primes.
* `leaf_shift_even_large`, the shift bookkeeping: if `N` is even and `M₀ + 4 < N` then `N - 2` is
  even and still above `M₀`, so the input applies to `N - 2`.
* `leaf_constant_family_in_window`, the power family: for `1 / 2 ≤ θ` and `4 ≤ N` the constant
  family `ν ≡ 1` stays inside the window, `2 ^ (ν i) = 2 ≤ N ^ θ`, and its powers sum to `2 * K`.

Assembly: take `K = 1` and `N₀ = M₀ + 4`. For an even `N > N₀` the shift step gives an even
`N - 2 > M₀`, the analytic input writes `N - 2 = p + q`, the family at `K = 1` writes `N - 2` as a
single power `2`, and then `N = p + q + ∑ i, 2 ^ (ν i)` with `2 * K = 2 ≤ ∑ i, 2 ^ (ν i)`.

Nothing here is proved: the three leaves stay open, and the assembly is sorry-free.
-/

namespace LeanLab.Linnik1951.Novelty1620

open LeanLab.Linnik LeanLab.DERZ1997

/-- LEAF. Step 1, the analytic input. Assume GRH. Then there is a threshold `M₀` such that every
even `m > M₀` is a sum of two primes, `m = p + q` with `p` and `q` prime. No powers of two occur in
this step; it is the statement that GRH makes every sufficiently large even integer a Goldbach
number, and it is the only step of the split that needs analysis. -/
theorem leaf_grh_even_goldbach (hG : GRH) :
    ∃ M₀ : ℕ, ∀ m : ℕ, Even m → M₀ < m →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p + q := by
  sorry

/-- LEAF. Step 2, the shift by two. If `N` is even and `M₀ + 4 < N` then `N - 2` is even and still
above `M₀`. So the analytic input can be applied to the shifted number `N - 2`, whose two prime
summands leave exactly the power `2` over. The `4` in the hypothesis keeps the truncated
subtraction `N - 2` away from `0` and `1`. -/
theorem leaf_shift_even_large {M₀ N : ℕ} (hEven : Even N) (hN : M₀ + 4 < N) :
    Even (N - 2) ∧ M₀ < N - 2 := by
  obtain ⟨k, rfl⟩ := hEven
  have hk3 : 3 ≤ k := by omega
  exact ⟨⟨k - 1, by omega⟩, by omega⟩

/-- LEAF. Step 3, the constant power family. For `1 / 2 ≤ θ` and `4 ≤ N` the family `ν ≡ 1` is a
family of `K` powers that stays inside the window, `1 ≤ ν i` and `2 ^ (ν i) = 2 ≤ N ^ θ`, and its
powers sum to `2 * K`. This is the `2 * K ≤ ∑ i, 2 ^ (ν i)` side of the target together with the
window bound on the individual powers, and it holds for the empty family at `K = 0` as well. -/
theorem leaf_constant_family_in_window {θ : ℝ} (hθ : 1 / 2 ≤ θ) {K N : ℕ} (hN : 4 ≤ N) :
    ∃ ν : Fin K → ℕ, (∀ i, 1 ≤ ν i ∧ (2 : ℝ) ^ (ν i) ≤ (N : ℝ) ^ θ) ∧
      ∑ i, 2 ^ (ν i) = 2 * K := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have h4N : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow]
    norm_num
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro i
    refine ⟨le_rfl, ?_⟩
    show (2 : ℝ) ^ (1 : ℕ) ≤ (N : ℝ) ^ θ
    rw [show (2 : ℝ) ^ (1 : ℕ) = 2 from by norm_num]
    calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := hfour.symm
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) h4N (by norm_num)
      _ ≤ (N : ℝ) ^ θ := Real.rpow_le_rpow_of_exponent_le hN1 hθ
  · simp [Finset.sum_const, Finset.card_univ, Nat.mul_comm]

/-- `leaf_grh_powers_within_window` of `SPLIT_linnik_low_bits`, assembled from the three leaves
above with `K = 1` and `N₀ = M₀ + 4`: the analytic input handles `N - 2`, the shift step keeps
`N - 2` even and large, and the family `ν ≡ 1` supplies the single power `2 = 2 * K`. -/
theorem leaf_grh_powers_within_window_split (hG : GRH) :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      ∃ K N₀ : ℕ, ∀ N : ℕ, Even N → N₀ < N →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
          ∃ t : ℕ, t ≤ K ∧ ∃ ν : Fin t → ℕ,
            (∀ i, 1 ≤ ν i ∧ (2 : ℝ) ^ (ν i) ≤ (N : ℝ) ^ θ) ∧
              N = p + q + ∑ i, 2 ^ (ν i) ∧ 2 * K ≤ ∑ i, 2 ^ (ν i) := by
  intro θ hθ1 hθ2
  obtain ⟨M₀, hM⟩ := leaf_grh_even_goldbach hG
  have hθhalf : 1 / 2 ≤ θ := le_of_lt hθ1
  refine ⟨1, M₀ + 4, ?_⟩
  intro N hEven hN
  obtain ⟨hEven', hlarge⟩ := leaf_shift_even_large (M₀ := M₀) hEven hN
  obtain ⟨p, q, hp, hq, hpq⟩ := hM (N - 2) hEven' hlarge
  have hN4 : 4 ≤ N := by omega
  obtain ⟨ν, hν, hsum⟩ := leaf_constant_family_in_window (θ := θ) (K := 1) (N := N) hθhalf hN4
  refine ⟨p, q, hp, hq, 1, le_rfl, ν, fun i => hν i, ?_, ?_⟩
  · rw [hsum]
    omega
  · rw [hsum]

end LeanLab.Linnik1951.Novelty1620
