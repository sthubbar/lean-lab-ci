/-
The coprime Mobius input from Granville and Ramare 1996 Lemma 10.2.
Source: https://dms.umontreal.ca/~andrew/PDF/ramare.pdf, preprint page 42.
Helfgott cites it on page 7 equation 2.7 of arXiv 1205.5252v4.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.Ramare1995.AristotleTrial05

namespace LeanLab.HelfgottArcs.Mobius325
open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- The Mobius function restricted to integers coprime to q.
Source: Granville and Ramare preprint page 42, Lemma 10.2. -/
noncomputable def coprimeMu (q : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n.Coprime q then (moebius : ArithmeticFunction ℝ) n else 0, by simp⟩

/-- The restricted Mobius function remains multiplicative.
Source: Granville and Ramare page 42, a derived input for the divisor identity. -/
theorem coprimeMu_multiplicative (q : ℕ) : (coprimeMu q).IsMultiplicative := by
  constructor
  · simp [coprimeMu]
  · intro m n hmn
    have hh := (isMultiplicative_moebius.intCast (R := ℝ)).map_mul_of_coprime hmn
    simp only [coprimeMu, ArithmeticFunction.coe_mk, Nat.coprime_mul_iff_left]
    rw [hh]
    split_ifs <;> simp_all

/-- At a positive prime power the divisor transform is one or zero.
Source: Granville and Ramare page 42, the inner divisor sum. -/
theorem coprimeMu_zeta_prime_pow (q p k : ℕ) (hp : p.Prime) :
    (coprimeMu q * (zeta : ArithmeticFunction ℝ)) (p ^ (k + 1)) =
      if p ∣ q then 1 else 0 := by
  by_cases hpq : p ∣ q
  · have hcp : ¬ p.Coprime q := by
      intro hc
      exact (hp.coprime_iff_not_dvd.mp hc) hpq
    rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, sum_range_succ']
    have hz : ∑ j ∈ range (k + 1), coprimeMu q (p ^ (j + 1)) = 0 := by
      apply sum_eq_zero
      intro j _
      simp only [coprimeMu, ArithmeticFunction.coe_mk,
        Nat.coprime_pow_left_iff (Nat.succ_pos j) p q]
      exact if_neg hcp
    rw [hz]
    simp [coprimeMu, hpq]
  · have hcp : p.Coprime q := hp.coprime_iff_not_dvd.mpr hpq
    have heq : (coprimeMu q * (zeta : ArithmeticFunction ℝ)) (p ^ (k + 1)) =
        ((moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ)) (p ^ (k + 1)) := by
      simp only [coe_mul_zeta_apply]
      apply sum_congr rfl
      intro d hd
      have hdc : d.Coprime q := (hcp.pow_left (k + 1)).of_dvd_left (Nat.dvd_of_mem_divisors hd)
      simp [coprimeMu, hdc]
    rw [heq, coe_moebius_mul_coe_zeta, if_neg hpq]
    simp [hp.ne_one]

/-- The divisor transform takes only the values zero and one.
Source: Granville and Ramare page 42, the coprime counting identity. -/
theorem coprimeMu_zeta_values (q n : ℕ) :
    (coprimeMu q * (zeta : ArithmeticFunction ℝ)) n = 0 ∨
      (coprimeMu q * (zeta : ArithmeticFunction ℝ)) n = 1 := by
  have hm := (coprimeMu_multiplicative q).mul isMultiplicative_zeta.natCast
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => exact Or.inr hm.map_one
  | prime_pow p k hp hk =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [coprimeMu_zeta_prime_pow q p j hp]
    split_ifs <;> simp
  | coprime a b _ha _hb hab ha' hb' =>
    rw [hm.map_mul_of_coprime hab]
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> simp_all

/-- The restricted coefficient has absolute value at most one.
Source: Granville and Ramare page 42, a derived coefficient bound. -/
theorem coprimeMu_abs (q n : ℕ) : |coprimeMu q n| ≤ 1 := by
  change |if n.Coprime q then ((moebius n : ℤ) : ℝ) else 0| ≤ 1
  by_cases hn : n.Coprime q
  · rw [ite_eq_left hn]
    exact_mod_cast (abs_moebius_le_one (n := n))
  · rw [ite_eq_right hn]
    norm_num

/-- Away from one the transform vanishes on integers coprime to q.
Source: Granville and Ramare page 42, the disjoint support observation. -/
theorem coprimeMu_zeta_zero_of_coprime (q n : ℕ) (hn : n ≠ 1) (hc : n.Coprime q) :
    (coprimeMu q * (zeta : ArithmeticFunction ℝ)) n = 0 := by
  have hh : (coprimeMu q * (zeta : ArithmeticFunction ℝ)) n =
      ((moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ)) n := by
    simp only [coe_mul_zeta_apply]
    apply sum_congr rfl
    intro d hd
    have hdc : d.Coprime q := hc.of_dvd_left (Nat.dvd_of_mem_divisors hd)
    simp [coprimeMu, hdc]
  rw [hh, coe_moebius_mul_coe_zeta]
  simp [ArithmeticFunction.one_apply, hn]

/-- The counting term and coefficient mass have disjoint support above one.
Source: Granville and Ramare page 42, the final counting argument. -/
theorem coprimeMu_complement_bound (q n : ℕ) (hn : n ≠ 1) :
    (coprimeMu q * (zeta : ArithmeticFunction ℝ)) n + |coprimeMu q n| ≤ 1 := by
  by_cases hc : n.Coprime q
  · rw [coprimeMu_zeta_zero_of_coprime q n hn hc, zero_add]
    exact coprimeMu_abs q n
  · have hz : coprimeMu q n = 0 := by simp [coprimeMu, hc]
    rw [hz, abs_zero, add_zero]
    rcases coprimeMu_zeta_values q n with hh | hh <;> rw [hh] <;> norm_num

/-- Swap the finite divisor count into a floor weighted coefficient sum.
Source: Granville and Ramare page 42, first displayed identity. -/
theorem coprimeMu_floor_sum (q N : ℕ) :
    ∑ n ∈ Icc 1 N, (coprimeMu q * (zeta : ArithmeticFunction ℝ)) n =
      ∑ n ∈ Icc 1 N, coprimeMu q n * (N / n : ℕ) := by
  simp only [coe_mul_zeta_apply]
  rw [LeanLab.Ramare1995.AristotleTrial05.sum_divisors_swap]
  apply sum_congr rfl
  intro n hn
  rw [sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
  ring

/-- Division with remainder splits a weighted reciprocal sum into a floor term and an error.
Source: Granville and Ramare page 42, first displayed identity. -/
theorem reciprocal_floor_identity (f : ℕ → ℝ) (N : ℕ) :
    (N : ℝ) * (∑ n ∈ Icc 1 N, f n / n) =
      (∑ n ∈ Icc 1 N, f n * (N / n : ℕ)) +
        ∑ n ∈ Icc 1 N, f n * ((N % n : ℕ) : ℝ) / n := by
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by have := (mem_Icc.mp hn).1; exact_mod_cast (by omega : n ≠ 0)
  have hh : (n : ℝ) * ((N / n : ℕ) : ℝ) + ((N % n : ℕ) : ℝ) = N := by
    exact_mod_cast Nat.div_add_mod N n
  field_simp
  rw [← hh]
  ring

/-- Granville and Ramare 1996 Lemma 10.2, at every integer endpoint.
Source: author preprint page 42 and Helfgott page 7 equation 2.7. -/
theorem coprime_mobius_reciprocal_bound (q N : ℕ) :
    |∑ n ∈ Icc 1 N, coprimeMu q n / n| ≤ 1 := by
  by_cases hN : N = 0
  · subst N; simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hb (n : ℕ) : 0 ≤ (coprimeMu q * (zeta : ArithmeticFunction ℝ)) n := by
    rcases coprimeMu_zeta_values q n with hh | hh <;> rw [hh] <;> norm_num
  have hid : (N : ℝ) * (∑ n ∈ Icc 1 N, coprimeMu q n / n) =
      ∑ n ∈ Icc 1 N, ((coprimeMu q * (zeta : ArithmeticFunction ℝ)) n +
        coprimeMu q n * ((N % n : ℕ) : ℝ) / n) := by
    rw [sum_add_distrib, coprimeMu_floor_sum]
    exact reciprocal_floor_identity (coprimeMu q) N
  have hs : |(N : ℝ) * (∑ n ∈ Icc 1 N, coprimeMu q n / n)| ≤ N := by
    rw [hid]
    calc
      _ ≤ ∑ n ∈ Icc 1 N, |(coprimeMu q * (zeta : ArithmeticFunction ℝ)) n +
          coprimeMu q n * ((N % n : ℕ) : ℝ) / n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) := by
        apply sum_le_sum
        intro n hn
        by_cases hn1 : n = 1
        · subst n
          have hb1 := ((coprimeMu_multiplicative q).mul isMultiplicative_zeta.natCast).map_one
          rw [hb1]
          simp only [Nat.mod_one, Nat.cast_zero, mul_zero, zero_div, add_zero, abs_one]
          exact le_rfl
        · have hnpos : (0 : ℝ) < n := by
            exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hn).1
          have hr0 : 0 ≤ ((N % n : ℕ) : ℝ) / n := by positivity
          have hr1 : ((N % n : ℕ) : ℝ) / n ≤ 1 := by
            rw [div_le_one hnpos]
            have hnNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hn).1
            exact_mod_cast (Nat.mod_lt N hnNat).le
          calc
            _ ≤ |(coprimeMu q * (zeta : ArithmeticFunction ℝ)) n| +
                |coprimeMu q n * ((N % n : ℕ) : ℝ) / n| := abs_add_le _ _
            _ = (coprimeMu q * (zeta : ArithmeticFunction ℝ)) n +
                |coprimeMu q n| * (((N % n : ℕ) : ℝ) / n) := by
              rw [abs_of_nonneg (hb n), mul_div_assoc, abs_mul, abs_of_nonneg hr0]
            _ ≤ (coprimeMu q * (zeta : ArithmeticFunction ℝ)) n + |coprimeMu q n| := by
              apply add_le_add le_rfl
              simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1 (abs_nonneg (coprimeMu q n))
            _ ≤ 1 := coprimeMu_complement_bound q n hn1
      _ = N := by simp
  rw [abs_mul, abs_of_pos hN0] at hs
  nlinarith

/-- Equation 2.7 with the literal coprime sum and a real endpoint.
Source: Helfgott page 7, citing Granville and Ramare 1996 Lemma 10.2. -/
theorem granville_ramare_10_2 (x : ℝ) (q : ℕ) :
    |∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n.Coprime q),
      ((moebius n : ℤ) : ℝ) / n| ≤ 1 := by
  have hh := coprime_mobius_reciprocal_bound q ⌊x⌋₊
  simpa only [sum_filter, coprimeMu, ArithmeticFunction.coe_mk,
    ArithmeticFunction.intCoe_apply, ite_div, zero_div] using hh

end LeanLab.HelfgottArcs.Mobius325
