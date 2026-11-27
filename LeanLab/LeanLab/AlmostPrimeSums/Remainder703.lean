import LeanLab.AlmostPrimeSums.Decomp1527c

/-!
AI wrote this Lean code for CODEX task703. Goldbach is open.
Finite per modulus prime sequence comparison for BJS p. 43 equation 141
and p. 53 equation 165, from the definitions on p. 35 equations 105 and 107.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Remainder703

open Finset Real
open LeanLab.AlmostPrimeSums.Decomp1527c

/-- Removing the primes dividing N and changing the prime count endpoint
costs at most the number of distinct prime divisors of N plus one. -/
theorem A_remainder_error_le703 (N d : ℕ) (hd1 : 1 ≤ d) :
    |(#((range N).filter (fun p => p.Prime ∧ ¬p ∣ N ∧ d ∣ N - p)) : ℝ)
      - (Nat.primeCounting N : ℝ) / (d.totient : ℝ)| ≤
      |(primesAP (N - 1) d N : ℝ)
        - (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)| +
        ((N.primeFactors.card : ℝ) + 1) := by
  have hpiNat : Nat.primeCounting (N - 1) ≤ Nat.primeCounting N ∧
      Nat.primeCounting N ≤ Nat.primeCounting (N - 1) + 1 := by
    constructor
    · exact Nat.monotone_primeCounting (Nat.sub_le _ _)
    · rw [Nat.primeCounting_sub_one, Nat.primeCounting_eq_primeCounting'_succ]
      unfold Nat.primeCounting'
      rw [Nat.count_succ]
      split_ifs <;> omega
  have hpi0 : (Nat.primeCounting (N - 1) : ℝ) ≤ Nat.primeCounting N := by
    exact_mod_cast hpiNat.1
  have hpi1 : (Nat.primeCounting N : ℝ) ≤ Nat.primeCounting (N - 1) + 1 := by
    exact_mod_cast hpiNat.2
  have hφ1 : (1 : ℝ) ≤ d.totient := by
    exact_mod_cast (show 1 ≤ d.totient by exact Nat.totient_pos.mpr hd1)
  have hφ0 : (0 : ℝ) ≤ d.totient := by linarith
  let a : ℝ := #((range N).filter (fun p => p.Prime ∧ ¬p ∣ N ∧ d ∣ N - p))
  let b : ℝ := primesAP (N - 1) d N
  let m₀ : ℝ := (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)
  let m : ℝ := (Nat.primeCounting N : ℝ) / (d.totient : ℝ)
  have ha : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (card_A_dvd N d).1
  have hb : b ≤ a + (N.primeFactors.card : ℝ) := by
    dsimp [a, b]
    exact_mod_cast (card_A_dvd N d).2
  have hm₀ : m₀ ≤ m := div_le_div_of_nonneg_right hpi0 hφ0
  have hm₁ : m ≤ m₀ + 1 := by
    have hh := div_le_div_of_nonneg_right hpi1 hφ0
    have h1 : (1 : ℝ) / d.totient ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hφ1
    dsimp [m, m₀]
    rw [add_div] at hh
    linarith
  change |a - m| ≤ |b - m₀| + ((N.primeFactors.card : ℝ) + 1)
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (b - m₀), le_abs_self (b - m₀),
    (show (0 : ℝ) ≤ N.primeFactors.card from Nat.cast_nonneg _)]

end LeanLab.AlmostPrimeSums.Remainder703
