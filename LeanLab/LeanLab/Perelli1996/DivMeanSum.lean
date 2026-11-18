/-
P0083 Perelli 1996, page 481 between equations 3 and 4 and page 487 equation 28, elementary divisor mean support.
Proves n ≤ φ(n) τ(n), k^ω(e) ≤ τ(e)^k, and a logarithmic bound for the sum of τ(e)^J / e.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Divisor103

namespace LeanLab.Perelli1996.DivMean
open Finset Real
open LeanLab.Perelli1996.Section2 LeanLab.Perelli1996.Divisor103

/-- Every positive integer is at most its totient times its number of divisors. -/
theorem self_le_totient_mul_card_divisors (m : ℕ) (hm : 0 < m) :
    m ≤ m.totient * m.divisors.card := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp
  | prime_pow p n hp hn =>
    obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
    have hcard : (p ^ (a + 1)).divisors.card = a + 2 := by
      rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    rw [Nat.totient_prime_pow hp hn, hcard, Nat.add_sub_cancel, pow_succ, mul_assoc]
    apply Nat.mul_le_mul_left
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
    have h2 : (q + 2 - 1) * 2 ≤ (q + 2 - 1) * (a + 2) := Nat.mul_le_mul_left _ (by omega)
    have h3 : q + 2 - 1 = q + 1 := by omega
    rw [h3] at h2 ⊢
    omega
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab, Nat.Coprime.card_divisors_mul hab]
    calc a * b ≤ (a.totient * a.divisors.card) * (b.totient * b.divisors.card) :=
          Nat.mul_le_mul (iha (by omega)) (ihb (by omega))
      _ = _ := by ring

/-- Two to the number of prime factors is at most the number of divisors. -/
theorem two_pow_card_primeFactors_le (e : ℕ) (he : 0 < e) :
    2 ^ e.primeFactors.card ≤ e.divisors.card := by
  rw [Nat.card_divisors he.ne']
  apply Finset.pow_card_le_prod
  intro p hp
  have : 0 < e.factorization p :=
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd he.ne'
      (Nat.dvd_of_mem_primeFactors hp)
  omega

/-- The power k to the number of prime factors is at most the k-th power of the divisor count. -/
theorem pow_card_primeFactors_le (k e : ℕ) (he : 0 < e) :
    k ^ e.primeFactors.card ≤ e.divisors.card ^ k := by
  calc k ^ e.primeFactors.card ≤ (2 ^ k) ^ e.primeFactors.card :=
        Nat.pow_le_pow_left k.lt_two_pow_self.le _
    _ = (2 ^ e.primeFactors.card) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ e.divisors.card ^ k := Nat.pow_le_pow_left (two_pow_card_primeFactors_le e he) k

/-- The number of divisors is the twofold divisor count. -/
theorem card_divisors_eq_divisorCount (e : ℕ) : e.divisors.card = divisorCount 2 e := by
  change _ = (ArithmeticFunction.zeta ^ 2) e
  rw [pow_two, ArithmeticFunction.mul_zeta_apply, Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ArithmeticFunction.zeta_apply_ne (Nat.pos_of_mem_divisors hi).ne']

/-- Iterated squaring of the divisor count is dominated by a higher divisor count. -/
theorem card_divisors_pow_two_pow_le (j e : ℕ) :
    e.divisors.card ^ (2 ^ j) ≤ divisorCount (2 ^ (2 ^ j)) e := by
  induction j with
  | zero => simp [card_divisors_eq_divisorCount]
  | succ j ih =>
    calc e.divisors.card ^ (2 ^ (j + 1)) = (e.divisors.card ^ (2 ^ j)) ^ 2 := by
          rw [← pow_mul, pow_succ]
      _ ≤ (divisorCount (2 ^ (2 ^ j)) e) ^ 2 := Nat.pow_le_pow_left ih 2
      _ ≤ divisorCount ((2 ^ (2 ^ j)) ^ 2) e := divisorCount_sq_le _ _
      _ = divisorCount (2 ^ (2 ^ (j + 1))) e := by rw [← pow_mul, pow_succ]

/-- The reciprocal weighted sum of powers of the divisor count has a logarithmic power bound. -/
theorem sum_card_divisors_pow_div_le (J Y : ℕ) :
    ∑ e ∈ Finset.Icc 1 Y, ((e.divisors.card : ℝ) ^ J) / (e : ℝ) ≤
      (1 + Real.log Y) ^ (2 ^ (2 ^ J)) := by
  have hset : Finset.Icc 1 Y = Finset.Ioc 0 Y := by ext n; simp; omega
  have hhar : 0 ≤ (harmonic Y : ℝ) := by
    rw [← weightedDivisor_one_sum]
    exact Finset.sum_nonneg (fun n _ => weightedDivisor_nonneg 1 n)
  rw [hset]
  calc ∑ e ∈ Finset.Ioc 0 Y, ((e.divisors.card : ℝ) ^ J) / (e : ℝ)
      ≤ ∑ e ∈ Finset.Ioc 0 Y, weightedDivisor (2 ^ (2 ^ J)) e := by
        apply Finset.sum_le_sum
        intro e he
        have he0 : 0 < e := (Finset.mem_Ioc.mp he).1
        have hc : 1 ≤ e.divisors.card :=
          Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr he0.ne'⟩
        have h1 : e.divisors.card ^ J ≤ divisorCount (2 ^ (2 ^ J)) e :=
          (Nat.pow_le_pow_right hc J.lt_two_pow_self.le).trans
            (card_divisors_pow_two_pow_le J e)
        change _ ≤ (divisorCount (2 ^ (2 ^ J)) e : ℝ) / (e : ℝ)
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg e)
        exact_mod_cast h1
    _ ≤ (harmonic Y : ℝ) ^ (2 ^ (2 ^ J)) := weightedDivisor_sum_le _ Y
    _ ≤ _ := pow_le_pow_left₀ hhar (harmonic_le_one_add_log Y) _

end LeanLab.Perelli1996.DivMean

#print axioms LeanLab.Perelli1996.DivMean.self_le_totient_mul_card_divisors
#print axioms LeanLab.Perelli1996.DivMean.pow_card_primeFactors_le
#print axioms LeanLab.Perelli1996.DivMean.sum_card_divisors_pow_div_le
