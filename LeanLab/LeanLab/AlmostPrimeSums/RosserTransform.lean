import Mathlib.NumberTheory.SelbergSieve

/-!
AI wrote this Lean code for CODEX task258. Goldbach is open.
Finite SelbergTerms identities for the Rosser main terms.
These are derived identities for Heath Brown pp. 30 to 35 and BJS p. 10.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset ArithmeticFunction BoundingSieve

/-- The sum of Selberg terms on multiples of a divisor is its density times
the total Selberg mass. Derived finite identity for Heath Brown p. 35. -/
theorem sum_selbergTerms_multiples (s : BoundingSieve) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    (∑ n ∈ s.prodPrimes.divisors, if d ∣ n then s.selbergTerms n else 0) =
      s.selbergTerms s.prodPrimes * s.nu d / s.nu s.prodPrimes := by
  classical
  have hc : ∀ n, n ∣ s.prodPrimes → (s.prodPrimes / n).Coprime n := by
    intro n hn
    exact Nat.coprime_of_squarefree_mul
      ((Nat.div_mul_cancel hn).symm ▸ s.prodPrimes_squarefree)
  have hcomp : ∀ n ∈ s.prodPrimes.divisors,
      s.selbergTerms (s.prodPrimes / n) =
        s.selbergTerms s.prodPrimes / s.selbergTerms n := by
    intro n hn
    exact s.selbergTerms_isMultiplicative.map_div_of_coprime
      (Nat.mem_divisors.mp hn).1 (hc n (Nat.mem_divisors.mp hn).1)
      (s.selbergTerms_pos (Nat.mem_divisors.mp hn).1).ne'
  have hcond : ∀ n ∈ s.prodPrimes.divisors,
      d ∣ s.prodPrimes / n ↔ n ∣ s.prodPrimes / d := by
    intro n hn
    rw [Nat.dvd_div_iff_mul_dvd (Nat.mem_divisors.mp hn).1,
      Nat.dvd_div_iff_mul_dvd hd, Nat.mul_comm]
  calc
    _ = ∑ n ∈ s.prodPrimes.divisors,
        if d ∣ s.prodPrimes / n then s.selbergTerms (s.prodPrimes / n) else 0 :=
      (Nat.sum_div_divisors s.prodPrimes _).symm
    _ = s.selbergTerms s.prodPrimes *
        ∑ n ∈ s.prodPrimes.divisors,
          if n ∣ s.prodPrimes / d then (s.selbergTerms n)⁻¹ else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [hcond n hn, hcomp n hn]
      split_ifs <;> simp [div_eq_mul_inv]
    _ = s.selbergTerms s.prodPrimes * (s.nu (s.prodPrimes / d))⁻¹ := by
      rw [← s.nu_inv_eq_sum_divisors_inv_selbergTerms (Nat.div_dvd_of_dvd hd)]
    _ = _ := by
      rw [s.nu_mult.map_div_of_coprime hd (hc d hd) (s.nu_ne_zero hd)]
      field_simp

/-- The full Selberg mass normalizes the sieve Euler product.
Derived finite normalization for Heath Brown p. 35 and BJS p. 10. -/
theorem selbergTerms_mul_eulerProduct (s : BoundingSieve) :
    s.selbergTerms s.prodPrimes *
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) = s.nu s.prodPrimes := by
  rw [s.selbergTerms_apply, Finset.prod_inv_distrib, mul_assoc,
    inv_mul_cancel₀, mul_one]
  exact Finset.prod_ne_zero_iff.mpr fun p hp =>
    (sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp))).ne'

/-- Multiples of d have total normalized Selberg mass g of d.
Derived finite marginal identity for Heath Brown p. 35. -/
theorem eulerProduct_mul_selbergTerms_multiples (s : BoundingSieve) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
      (∑ n ∈ s.prodPrimes.divisors, if d ∣ n then s.selbergTerms n else 0) =
        s.nu d := by
  rw [sum_selbergTerms_multiples s hd]
  have he := selbergTerms_mul_eulerProduct s
  have hn := s.nu_ne_zero (dvd_refl s.prodPrimes)
  calc
    _ = (s.selbergTerms s.prodPrimes *
        ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) * s.nu d /
          s.nu s.prodPrimes := by ring
    _ = s.nu d := by rw [he]; field_simp

/-- A divisor main sum is an average of divisor sums with positive Selberg
mass. Derived finite transform for Heath Brown pp. 31 to 35. -/
theorem mainSum_eq_selberg_average (s : BoundingSieve) (lam : ℕ → ℝ) :
    s.mainSum lam =
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        ∑ n ∈ s.prodPrimes.divisors,
          s.selbergTerms n * ∑ d ∈ n.divisors, lam d := by
  classical
  have hinner : ∀ n ∈ s.prodPrimes.divisors,
      (∑ d ∈ n.divisors, lam d) =
        ∑ d ∈ s.prodPrimes.divisors, if d ∣ n then lam d else 0 := by
    intro n hn
    rw [← Finset.sum_filter,
      Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero (Nat.mem_divisors.mp hn).1]
  symm
  calc
    _ = (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        ∑ n ∈ s.prodPrimes.divisors, ∑ d ∈ s.prodPrimes.divisors,
          if d ∣ n then s.selbergTerms n * lam d else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [hinner n hn, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
    _ = ∑ d ∈ s.prodPrimes.divisors, lam d * s.nu d := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hm := eulerProduct_mul_selbergTerms_multiples s (Nat.mem_divisors.mp hd).1
      calc
        _ = ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
            ∑ n ∈ s.prodPrimes.divisors, if d ∣ n then s.selbergTerms n else 0) * lam d := by
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro n _
          split_ifs <;> simp
        _ = lam d * s.nu d := by rw [hm]; ring

/-- The Selberg average of the indicator of one is one.
Derived finite identity for Heath Brown pp. 31 to 35. -/
theorem selberg_average_indicator_one (s : BoundingSieve) :
    (∑ n ∈ s.prodPrimes.divisors,
      s.selbergTerms n * (if n = 1 then 1 else 0)) = 1 := by
  classical
  simp [s.selbergTerms_apply, s.nu_mult.map_one, s.prodPrimes_ne_zero]

/-- Divisor sum comparisons pass to main sums through positive Selberg mass.
Derived order principle for Heath Brown pp. 31 to 35. -/
theorem mainSum_mono_of_divisor_sum (s : BoundingSieve) (lam eta : ℕ → ℝ)
    (h : ∀ n, n ∣ s.prodPrimes →
      ∑ d ∈ n.divisors, lam d ≤ ∑ d ∈ n.divisors, eta d) :
    s.mainSum lam ≤ s.mainSum eta := by
  rw [mainSum_eq_selberg_average, mainSum_eq_selberg_average]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_left (h n (Nat.mem_divisors.mp hn).1)
      (s.selbergTerms_pos (Nat.mem_divisors.mp hn).1).le
  · exact Finset.prod_nonneg fun p hp =>
      (sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp))).le

/-- Main term deviation is exactly the normalized positive mass average of
the divisor sum defect. Derived finite identity for Heath Brown pp. 31 to 35. -/
theorem mainSum_sub_eulerProduct_eq (s : BoundingSieve) (lam : ℕ → ℝ) :
    s.mainSum lam - (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) =
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        ∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n *
          ((∑ d ∈ n.divisors, lam d) - (if n = 1 then 1 else 0)) := by
  rw [mainSum_eq_selberg_average]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, selberg_average_indicator_one]
  ring

/-- Upper divisor weights have main sum at least V. Lower divisor weights
have main sum at most V. Derived finite sign principle for Heath Brown p. 35. -/
theorem mainSum_eulerProduct_signs (s : BoundingSieve) (lp lm : ℕ → ℝ)
    (hp : ∀ n, n ∣ s.prodPrimes →
      (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, lp d)
    (hm : ∀ n, n ∣ s.prodPrimes →
      ∑ d ∈ n.divisors, lm d ≤ if n = 1 then 1 else 0) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) ≤ s.mainSum lp ∧
      s.mainSum lm ≤ ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  have hV : 0 ≤ ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
    Finset.prod_nonneg fun p hp =>
      (sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp))).le
  have hplus : 0 ≤ ∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n *
      ((∑ d ∈ n.divisors, lp d) - (if n = 1 then 1 else 0)) :=
    Finset.sum_nonneg fun n hn => mul_nonneg
      (s.selbergTerms_pos (Nat.mem_divisors.mp hn).1).le
      (sub_nonneg.mpr (hp n (Nat.mem_divisors.mp hn).1))
  have hminus : ∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n *
      ((∑ d ∈ n.divisors, lm d) - (if n = 1 then 1 else 0)) ≤ 0 :=
    Finset.sum_nonpos fun n hn => mul_nonpos_of_nonneg_of_nonpos
      (s.selbergTerms_pos (Nat.mem_divisors.mp hn).1).le
      (sub_nonpos.mpr (hm n (Nat.mem_divisors.mp hn).1))
  constructor
  · have hh := mul_nonneg hV hplus
    rw [← mainSum_sub_eulerProduct_eq] at hh
    exact sub_nonneg.mp hh
  · have hh := mul_nonpos_of_nonneg_of_nonpos hV hminus
    rw [← mainSum_sub_eulerProduct_eq] at hh
    exact sub_nonpos.mp hh

end LeanLab.AlmostPrimeSums.Decomp1527b
