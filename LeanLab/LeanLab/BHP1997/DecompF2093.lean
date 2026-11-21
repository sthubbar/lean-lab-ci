/-
Split of `upper_mean_value_supply` from `Decomp312b.lean` for FREE-nv-glm task2093.

The assembly uses the prime coefficient family on both sides of the short
approximation. The sifted family agrees with the prime family on every long
window for all sufficiently large x. The remaining analytic inputs are the
character mean value and the reference density for the prime family.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312b

namespace LeanLab.BHP1997.DecompF2093
open Classical Complex DecompC165b Decomp312a Decomp312c Decomp312b Decomp132
open scoped BigOperators

/-- The assembled upper supply. Its conclusion is copied from the target theorem.
The proof is a short chain of the seven leaves below. -/
theorem upper_mean_value_supply_F2093 (h4 : Thm4.Theorem4Paper) : ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η → ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u1 b ∧
        ShortApproximation ε (section4SiftedFamily c1) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k := by
  obtain ⟨B0, η, u1, hB0, hη, hη10, hu1, hu1'⟩ :=
    leaf_f2093_numeric_constants
  refine ⟨B0, η, lt_of_lt_of_le zero_lt_one hB0, hη, ?_⟩
  intro ε hε hεη
  have hεsmall : ε < 9 / 20 := lt_of_lt_of_le hεη (lt_of_le_of_lt hη10 (by norm_num))
  have hc := leaf_f2093_sifted_divisor_bound B0 hB0
  have hb := leaf_f2093_auxiliary_divisor_bound B0 hB0
  have hm := leaf_f2093_prime_mean_value ε hε hεsmall
  have hd := leaf_f2093_prime_reference_density u1 hu1 hu1'
  have happ := leaf_f2093_prime_short_approximation ε hε hεsmall
  have hdom := leaf_f2093_prime_domination ε hε hεsmall
  exact ⟨u1, fun _ k => primeWeight k, fun _ k => primeWeight k,
    hu1, hu1', hc, hb, hm, hd, happ, hdom⟩

/-- LEAF. Numeric constants for the supply. There are a divisor exponent at least one,
a positive error threshold at most one tenth, and a density constant in the required
half-open interval. The sample values one, one tenth, and one satisfy every bound. -/
theorem leaf_f2093_numeric_constants :
    ∃ B0 η u1 : ℝ, 1 ≤ B0 ∧ 0 < η ∧ η ≤ 1 / 10 ∧ 1 ≤ u1 ∧ u1 < 1.0001 := by
  exact ⟨1, 1 / 10, 1, by norm_num⟩

/-- LEAF. Divisor estimate for the sifted prime family. The section four sifted
family built from the prime indicator is bounded by the divisor count raised to any
exponent at least one. The sample prime 2 has two divisors, so the estimate is
nonzero. -/
theorem leaf_f2093_sifted_divisor_bound (B0 : ℝ) (hB0 : 1 ≤ B0) :
    ∃ C : ℝ, ∀ x k, |section4SiftedFamily (fun _ k => primeWeight k) x k| ≤
      C * ((k.divisors.card : ℕ) : ℝ) ^ B0 := by
  refine ⟨1, ?_⟩
  intro x k
  by_cases hk : k.Prime
  · have ht : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr
        ⟨1, Nat.one_mem_divisors.mpr hk.ne_zero⟩
    have hp : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) ^ B0 :=
      Real.one_le_rpow ht (by linarith)
    simp only [section4SiftedFamily, primeWeight, if_pos hk, one_mul]
    unfold siftedWeight
    split_ifs
    · simpa using hp
    · simpa using (le_trans zero_le_one hp)
  · simp only [section4SiftedFamily, primeWeight, if_neg hk, zero_mul, abs_zero, one_mul]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- LEAF. Divisor estimate for the auxiliary prime family. The prime indicator is
bounded by the divisor count raised to any exponent at least one. The sample prime 2
has two divisors, so the estimate is nonzero. -/
theorem leaf_f2093_auxiliary_divisor_bound (B0 : ℝ) (hB0 : 1 ≤ B0) :
    ∃ C : ℝ, ∀ x k, |(fun _ k => primeWeight k) x k| ≤
      C * ((k.divisors.card : ℕ) : ℝ) ^ B0 := by
  refine ⟨1, ?_⟩
  intro x k
  by_cases hk : k.Prime
  · have ht : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr
        ⟨1, Nat.one_mem_divisors.mpr hk.ne_zero⟩
    have hp : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) ^ B0 :=
      Real.one_le_rpow ht (by linarith)
    simp only [primeWeight, if_pos hk, abs_of_nonneg, one_mul]
    exact hp
  · simp only [primeWeight, if_neg hk, abs_zero, zero_le_one]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- LEAF. Character mean-value estimate for the prime family. For a small positive
error parameter, the weighted character sum over the long interval is bounded by the
square-root power with every logarithmic saving. The sample error one twentieth is
inside the permitted range. -/
theorem leaf_f2093_prime_mean_value (ε : ℝ) (hε : 0 < ε) (hεrange : ε < 9 / 20) :
    MeanValue41 ε (fun _ k => primeWeight k) := by
  sorry

/-- LEAF. Reference-density estimate for the prime family. For a density constant in
the required range, the normalized short-window character average has the principal
main term and vanishes for every other character, with every logarithmic saving. The
sample density one is the lower endpoint of the required range. -/
theorem leaf_f2093_prime_reference_density (u1 : ℝ) (hu1 : 1 ≤ u1)
    (hu1' : u1 < 1.0001) :
    ReferenceDensity u1 (fun _ k => primeWeight k) := by
  sorry

/-- LEAF. Short-window approximation estimate for the two prime families. The sifted
prime family equals the prime family on every long window for all sufficiently large
x. Hence the absolute difference sum is zero eventually. The sample window at x equal
to 100 has the same eventual equality mechanism. -/
theorem leaf_f2093_prime_short_approximation (ε : ℝ) (hε : 0 < ε)
    (hεrange : ε < 9 / 20) :
    ShortApproximation ε (section4SiftedFamily (fun _ k => primeWeight k))
      (fun _ k => primeWeight k) := by
  intro A hA
  obtain ⟨Xeq, heq⟩ := Filter.eventually_atTop.mp
    (prime_sifted_eventually_on_left hεrange)
  refine ⟨1, max Xeq 1, ?_⟩
  intro x hx
  have hxX : Xeq ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxpow : 0 ≤ x ^ (11 / 20 + ε : ℝ) :=
    Real.rpow_nonneg hx1 _
  have hlogpow : 0 ≤ Real.log x ^ (-A : ℝ) := Real.rpow_nonneg hlog _
  rw [Finset.sum_eq_zero]
  intro k hk
  rw [heq x hxX k hk]
  simp only [primeWeight, ite_self, abs_zero, sub_zero]
  exact mul_nonneg (mul_nonneg (by norm_num) hxpow) hlogpow

/-- LEAF. Eventual prime-domination estimate. The sifted prime family equals the
prime family on every long window for all sufficiently large x, and therefore
dominates the prime indicator there. The sample window at x equal to 100 has the same
eventual equality mechanism. -/
theorem leaf_f2093_prime_domination (ε : ℝ) (hε : 0 < ε)
    (hεrange : ε < 9 / 20) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ k ∈ leftInterval ε x, primeWeight k ≤
        section4SiftedFamily (fun _ k => primeWeight k) x k := by
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    (prime_sifted_eventually_on_left hεrange)
  refine ⟨X, ?_⟩
  intro x hx k hk
  rw [hX x hx k hk]
  exact le_rfl

end LeanLab.BHP1997.DecompF2093
