/-
Elementary local supplies for the three-square coefficient power bound.
Source page 13 properties i and ii and page 14 display 47.
The three local leaves have clean supplies. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp403d
import LeanLab.KumchevLiu2007.Decomp438e
import LeanLab.KumchevLiu2007.Decomp438f
import LeanLab.KumchevLiu2007.Decomp438g

namespace LeanLab.KumchevLiu2007.Task438d

open Real Complex Task129b Task129c
open scoped BigOperators

/-- LEAF. Page 13 property i. Schwarz page 83 Lemma 2.4.
Only the Chinese remainder factorization of one coefficient is required. -/
theorem A3_coprime_mul (n a b : ℕ) (hab : a.Coprime b) :
    A3 n (a * b) = A3 n a * A3 n b := by
  exact Task438e.A3_coprime_mul n a b hab

/-- LEAF. Page 14 sentence before display 47. A coarse uniform odd prime
bound suffices. Schwarz page 83 display 2.11 gives the count route.
The constant 8 covers the prime 3 and the reciprocal square error. -/
theorem A3_odd_prime_bound (n p : ℕ) (hp : p.Prime) (hodd : 2 < p) :
    ‖A3 n p‖ ≤ 8 / (p : ℝ) := by
  exact Task438g.A3_odd_prime_bound n p hp hodd

/-- LEAF. Page 13 property ii. Schwarz page 82 Lemma 2.1.
Odd prime powers vanish from exponent 2. Powers of 2 vanish from exponent 4.
This statement keeps the coefficients at 2, 4 and 8. -/
theorem A3_prime_power_vanish (n p k : ℕ) (hp : p.Prime)
    (hk : (p ≠ 2 ∧ 2 ≤ k) ∨ (p = 2 ∧ 4 ≤ k)) :
    A3 n (p ^ k) = 0 := by
  exact Task438f.A3_prime_power_vanish n p k hp hk

/-- Page 13 display 45. The modulus one coefficient is one. -/
theorem A3_one (n : ℕ) : A3 n 1 = 1 := by
  simp [A3, U1534.gaussS, U1534.ee]

/-- Page 13 property ii. The elementary totient bound retains all three
dyadic coefficients and supplies the constant 64 after multiplication by q. -/
theorem A3_small_dyadic_bound (n k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3) :
    ‖A3 n (2 ^ k)‖ ≤ 64 / ((2 ^ k : ℕ) : ℝ) := by
  have hb := Task403d.A3_norm_le_totient n (2 ^ k)
  have ht : ((Nat.totient (2 ^ k) : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.totient_le _)
  have hb' := hb.trans ht
  interval_cases k <;> norm_num at hb' ⊢ <;> linarith

/-- Page 14 display 47, local input for the composite estimate.
The odd prime bound and prime power vanishing are proved. -/
theorem A3_prime_power_bound (n p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ‖A3 n (p ^ k)‖ ≤ 64 / ((p ^ k : ℕ) : ℝ) := by
  by_cases htwo : p = 2
  · subst p
    by_cases hsmall : k ≤ 3
    · exact A3_small_dyadic_bound n k hk hsmall
    · rw [A3_prime_power_vanish n 2 k hp (Or.inr ⟨rfl, by omega⟩), norm_zero]
      positivity
  · by_cases hone : k = 1
    · subst k
      simp only [pow_one]
      have hp2 := hp.two_le
      exact (A3_odd_prime_bound n p hp (by omega)).trans (by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity))
    · rw [A3_prime_power_vanish n p k hp (Or.inl ⟨htwo, by omega⟩), norm_zero]
      positivity

/-- Page 14 display 47. A numerical majorant with one constant per distinct
prime divisor. The even prime is counted once even when its exponent is 3. -/
noncomputable def coefficientMajorant (q : ℕ) : ℝ :=
  ∏ _p ∈ q.primeFactors, (64 : ℝ)

/-- Page 14 display 47. Multiplying the local prime power bounds gives a
composite bound from the three proved local coefficient inputs. -/
theorem coefficient_product_bound (n q : ℕ) (hq : 0 < q) :
    ‖A3 n q‖ ≤ coefficientMajorant q / (q : ℝ) := by
  have hall : ∀ q : ℕ, 0 < q → ‖A3 n q‖ ≤ coefficientMajorant q / (q : ℝ) := by
    intro q
    induction q using Nat.recOnPrimeCoprime with
    | zero => intro h; omega
    | prime_pow p k hp =>
      intro hq
      by_cases hk : k = 0
      · subst k
        simp [A3_one, coefficientMajorant]
      · rw [coefficientMajorant, Nat.primeFactors_prime_pow hk hp]
        simpa using A3_prime_power_bound n p k hp (Nat.pos_of_ne_zero hk)
    | coprime a b ha hb hab ih_a ih_b =>
      intro hq
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hdis := hab.disjoint_primeFactors
      have hM : coefficientMajorant (a * b) = coefficientMajorant a * coefficientMajorant b := by
        simp only [coefficientMajorant, Nat.primeFactors_mul ha0 hb0, Finset.prod_union hdis]
      rw [A3_coprime_mul n a b hab, norm_mul, hM, Nat.cast_mul]
      calc
        _ ≤ (coefficientMajorant a / (a : ℝ)) * (coefficientMajorant b / (b : ℝ)) :=
          mul_le_mul (ih_a (by omega)) (ih_b (by omega)) (norm_nonneg _)
            ((norm_nonneg _).trans (ih_a (by omega)))
        _ = _ := by ring
  exact hall q hq

/-- Page 14 display 47 and page 15 third display. The conservative numerical
majorant has arbitrary positive power growth by separating finitely many primes. -/
theorem coefficientMajorant_power_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, 0 < q →
      coefficientMajorant q ≤ K * (q : ℝ) ^ ε := by
  classical
  let N : ℕ := ⌈(64 : ℝ) ^ ε⁻¹⌉₊
  refine ⟨(64 : ℝ) ^ N, by positivity, ?_⟩
  intro q hq
  let S := q.primeFactors.filter (fun p => p < N)
  let T := q.primeFactors.filter (fun p => ¬ p < N)
  have hS : (∏ _p ∈ S, (64 : ℝ)) ≤ (64 : ℝ) ^ N := by
    rw [Finset.prod_const]
    apply pow_le_pow_right₀ (by norm_num)
    have hsub : S ⊆ Finset.range N := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hsub
  have hT : (∏ _p ∈ T, (64 : ℝ)) ≤ (q : ℝ) ^ ε := by
    calc
      _ ≤ ∏ p ∈ T, (p : ℝ) ^ ε := by
        apply Finset.prod_le_prod₀ (fun p hp => by positivity)
        intro p hp
        have hpN : (64 : ℝ) ^ ε⁻¹ ≤ (p : ℝ) :=
          (Nat.le_ceil _).trans (by
            exact_mod_cast (Nat.le_of_not_gt (Finset.mem_filter.mp hp).2))
        have hb := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 64 ^ ε⁻¹) hpN hε.le
        rwa [Real.rpow_inv_rpow (by norm_num) hε.ne'] at hb
      _ = (∏ p ∈ T, (p : ℝ)) ^ ε :=
        Real.finsetProd_rpow T (fun p => (p : ℝ)) (fun p hp => by positivity) ε
      _ ≤ (q : ℝ) ^ ε := by
        apply Real.rpow_le_rpow (by positivity) _ hε.le
        have hprod : ∏ p ∈ T, p ≤ q := by
          apply Nat.le_of_dvd hq
          exact (Finset.prod_dvd_prod_of_subset T q.primeFactors (fun p => p)
            (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd q)
        have hc : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hprod
        simpa only [Nat.cast_prod] using hc
  rw [coefficientMajorant,
    ← Finset.prod_filter_mul_prod_filter_not q.primeFactors (fun p => p < N)]
  exact mul_le_mul hS hT (by positivity) (by positivity)

/-- Page 14 display 47. Exact Task438c coefficient leaf from three elementary
local inputs and the proved numerical product bound. -/
theorem coefficient_power_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ n q : ℕ, 0 < q →
      ‖A3 n q‖ ≤ K * (q : ℝ) ^ (1 / 8 : ℝ) / (q : ℝ) := by
  obtain ⟨K, hK, hb⟩ := coefficientMajorant_power_bound (1 / 8 : ℝ) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro n q hq
  exact (coefficient_product_bound n q hq).trans
    (div_le_div_of_nonneg_right (hb q hq) (by positivity))

end LeanLab.KumchevLiu2007.Task438d
