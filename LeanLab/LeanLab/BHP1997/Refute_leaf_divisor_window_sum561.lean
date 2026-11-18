/-
Refutation of the statement of `Decomp561e.leaf_divisor_window_sum561` in
`SPLIT_leaf_coefficient_energies561.lean`. That statement asks, for every real `B`,
for a constant `K` with the window sum of `d(k)^(2B)` over the `2Y` integers directly
below `x` at most `K * Y * log x ^ (2|B| + 4)`, for ALL `1 ≤ Y` and `2Y ≤ x`.
It fails at `B = 1`: take `Y = 1` and `x = 210^a`. The window holds `k = 210^a`,
which has `(a+1)^4` divisors, so the left side is at least `(a+1)^8`, while the right
side is `K * (a * log 210)^6`. A single integer can have more divisors than any fixed
power of its logarithm, so a window of bounded length carries no such bound.
The statement on main is not changed here; this file only records the proved negation.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD

namespace LeanLab.BHP1997.Refute561
open ArithmeticFunction

/-- The number of divisors of `210^a` is `(a+1)^4`, by multiplicativity of the divisor
function over the four primes 2, 3, 5, 7. Standard. -/
theorem card_divisors_210_pow (a : ℕ) : ((210 : ℕ) ^ a).divisors.card = (a + 1) ^ 4 := by
  have h210 : (210 : ℕ) ^ a = 2 ^ a * 3 ^ a * 5 ^ a * 7 ^ a := by
    rw [← mul_pow, ← mul_pow, ← mul_pow]
    norm_num
  have c1 : Nat.Coprime (2 ^ a * 3 ^ a * 5 ^ a) (7 ^ a) := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have c2 : Nat.Coprime (2 ^ a * 3 ^ a) (5 ^ a) := by
    rw [← mul_pow]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have c3 : Nat.Coprime (2 ^ a) (3 ^ a) := Nat.Coprime.pow _ _ (by norm_num)
  have p7 : Nat.Prime 7 := by norm_num
  rw [h210, ← sigma_zero_apply,
    isMultiplicative_sigma.map_mul_of_coprime c1,
    isMultiplicative_sigma.map_mul_of_coprime c2,
    isMultiplicative_sigma.map_mul_of_coprime c3,
    sigma_zero_apply_prime_pow Nat.prime_two, sigma_zero_apply_prime_pow Nat.prime_three,
    sigma_zero_apply_prime_pow Nat.prime_five, sigma_zero_apply_prime_pow p7]
  ring

/-- The window divisor moment bound, in the exact shape of
`Decomp561e.leaf_divisor_window_sum561`, is false at `B = 1`. -/
theorem divisor_window_sum561_fails_at_one :
    ¬ ∃ K : ℝ, 1 ≤ K ∧ ∀ Y x : ℝ, 1 ≤ Y → 2 * Y ≤ x →
      ∑ k ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊, (((k.divisors.card : ℕ) : ℝ) ^ (1 : ℝ)) ^ 2 ≤
        K * Y * Real.log x ^ (2 * |(1 : ℝ)| + 4) := by
  rintro ⟨K, hK, h⟩
  obtain ⟨a, ha⟩ := exists_nat_gt ((209 : ℝ) ^ 3 * K)
  have haK : (209 : ℝ) ^ 3 * K < a := ha
  have ha0 : (0 : ℝ) < a := by nlinarith
  have hN1 : 1 ≤ (210 : ℕ) ^ a := Nat.one_le_pow _ _ (by norm_num)
  have hapos : 0 < a := by exact_mod_cast ha0
  have hN2 : 2 ≤ (210 : ℕ) ^ a :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 210) hapos)
  have hx : (2 : ℝ) * 1 ≤ (((210 : ℕ) ^ a : ℕ) : ℝ) := by
    rw [mul_one]; exact_mod_cast hN2
  have hmain := h 1 (((210 : ℕ) ^ a : ℕ) : ℝ) le_rfl hx
  have hfl : ⌊(((210 : ℕ) ^ a : ℕ) : ℝ)⌋₊ = 210 ^ a := Nat.floor_natCast _
  have hfl2 : ⌊(((210 : ℕ) ^ a : ℕ) : ℝ) - 2 * 1⌋₊ = 210 ^ a - 2 := by
    rw [mul_one, Nat.floor_sub_ofNat, hfl]
  rw [hfl, hfl2] at hmain
  have hmem : (210 : ℕ) ^ a ∈ Finset.Ioc (210 ^ a - 2) (210 ^ a) := by
    rw [Finset.mem_Ioc]; omega
  have hterm : (((((210 : ℕ) ^ a).divisors.card : ℕ) : ℝ) ^ (1 : ℝ)) ^ 2 ≤
      ∑ k ∈ Finset.Ioc (210 ^ a - 2) (210 ^ a),
        (((k.divisors.card : ℕ) : ℝ) ^ (1 : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun k : ℕ => (((k.divisors.card : ℕ) : ℝ) ^ (1 : ℝ)) ^ 2)
      (fun k _ => sq_nonneg _) hmem
  rw [card_divisors_210_pow, Real.rpow_one] at hterm
  have hexp : (2 * |(1 : ℝ)| + 4) = ((6 : ℕ) : ℝ) := by rw [abs_one]; norm_num
  have hlog : Real.log (((210 : ℕ) ^ a : ℕ) : ℝ) = a * Real.log 210 := by
    push_cast
    rw [Real.log_pow]
  rw [hexp, Real.rpow_natCast, hlog, mul_one] at hmain
  have hl0 : (0 : ℝ) ≤ Real.log 210 := Real.log_nonneg (by norm_num)
  have hl1 : Real.log 210 ≤ 209 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 210)
    linarith
  have hpow : ((a : ℝ) * Real.log 210) ^ 6 ≤ ((a : ℝ) * 209) ^ 6 :=
    pow_le_pow_left₀ (mul_nonneg ha0.le hl0) (mul_le_mul_of_nonneg_left hl1 ha0.le) 6
  have hle : ((((a + 1) ^ 4 : ℕ) : ℝ)) ^ 2 ≤ K * ((a : ℝ) * 209) ^ 6 :=
    le_trans (le_trans hterm hmain) (mul_le_mul_of_nonneg_left hpow (by linarith))
  have h8 : (a : ℝ) ^ 8 < ((((a + 1) ^ 4 : ℕ) : ℝ)) ^ 2 := by
    push_cast
    rw [← pow_mul]
    exact pow_lt_pow_left₀ (by linarith) ha0.le (by norm_num)
  have hsq : (209 : ℝ) ^ 6 * K < (a : ℝ) ^ 2 := by
    have h1 : ((209 : ℝ) ^ 3 * K) ^ 2 < (a : ℝ) ^ 2 :=
      pow_lt_pow_left₀ haK (by positivity) (by norm_num)
    have h2 : (209 : ℝ) ^ 6 * K ≤ ((209 : ℝ) ^ 3 * K) ^ 2 := by
      have : K ≤ K ^ 2 := by nlinarith
      calc (209 : ℝ) ^ 6 * K ≤ (209 : ℝ) ^ 6 * K ^ 2 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = ((209 : ℝ) ^ 3 * K) ^ 2 := by ring
    linarith
  have h6 : (0 : ℝ) < (a : ℝ) ^ 6 := by positivity
  have hfin : K * ((a : ℝ) * 209) ^ 6 < (a : ℝ) ^ 8 := by
    calc K * ((a : ℝ) * 209) ^ 6 = (a : ℝ) ^ 6 * ((209 : ℝ) ^ 6 * K) := by ring
      _ < (a : ℝ) ^ 6 * (a : ℝ) ^ 2 := mul_lt_mul_of_pos_left hsq h6
      _ = (a : ℝ) ^ 8 := by ring
  linarith

/-- Consequence: the universally quantified statement of
`Decomp561e.leaf_divisor_window_sum561` is false. -/
theorem divisor_window_sum561_statement_false :
    ¬ ∀ B : ℝ, ∃ K : ℝ, 1 ≤ K ∧ ∀ Y x : ℝ, 1 ≤ Y → 2 * Y ≤ x →
      ∑ k ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊, (((k.divisors.card : ℕ) : ℝ) ^ B) ^ 2 ≤
        K * Y * Real.log x ^ (2 * |B| + 4) :=
  fun h => divisor_window_sum561_fails_at_one (h 1)

end LeanLab.BHP1997.Refute561
