/-
Elementary parameter bounds in Brun's pure sieve.
Source: Brun 1919, page 125, display 9 and the estimates above it.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.SchnirelmannGoldbach.PureSieveMain

open Finset
open scoped Classical

namespace LeanLab.SchnirelmannGoldbach.PureSieve

/-- The source constant 3 gives a factorial lower bound at every natural index. -/
theorem factorial_ge_third_power (j : ℕ) : ((j : ℝ) / 3) ^ j ≤ (j.factorial : ℝ) := by
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have h := Real.pow_div_factorial_le_exp (j : ℝ) (Nat.cast_nonneg j) j
  have he : Real.exp (j : ℝ) ≤ (3 : ℝ) ^ j := by
    calc Real.exp (j : ℝ) = Real.exp ((j : ℝ) * 1) := by rw [mul_one]
      _ = (Real.exp 1) ^ j := Real.exp_nat_mul 1 j
      _ ≤ (3 : ℝ) ^ j := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le j
  rw [div_le_iff₀ hf] at h
  rw [div_pow, div_le_iff₀ (by positivity)]
  calc (j : ℝ) ^ j ≤ Real.exp j * j.factorial := h
    _ ≤ 3 ^ j * j.factorial := mul_le_mul_of_nonneg_right he hf.le
    _ = j.factorial * 3 ^ j := mul_comm _ _

/-- Brun's factorial tail has the elementary envelope from page 125. -/
theorem factorial_tail_le (S : ℝ) (hS : 0 ≤ S) (j : ℕ) (hj : 0 < j) :
    S ^ j / j.factorial ≤ (3 * S / j) ^ j := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  calc S ^ j / j.factorial ≤ S ^ j / ((j : ℝ) / 3) ^ j :=
        div_le_div_of_nonneg_left (pow_nonneg hS _) (by positivity) (factorial_ge_third_power j)
    _ = (S / ((j : ℝ) / 3)) ^ j := (div_pow _ _ _).symm
    _ = (3 * S / j) ^ j := by congr 1; field_simp

/-- The finite binomial error is bounded by the power used in Brun display 9. -/
theorem binomial_remainder_le (R k : ℕ) (hR : 0 < R) :
    ∑ j ∈ range (k + 1), (R.choose j : ℝ) * 2 ^ j ≤ (2 * (R : ℝ)) ^ (k + 1) := by
  have hB : (2 : ℝ) ≤ 2 * R := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hgeom : ∀ k : ℕ, ∑ j ∈ range (k + 1), (2 * (R : ℝ)) ^ j ≤
      (2 * (R : ℝ)) ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using (show (1 : ℝ) ≤ 2 * R by linarith)
    | succ k ih =>
      rw [sum_range_succ, pow_succ (2 * (R : ℝ)) (k + 1)]
      have hp : 0 ≤ (2 * (R : ℝ)) ^ (k + 1) := by positivity
      nlinarith
  calc ∑ j ∈ range (k + 1), (R.choose j : ℝ) * 2 ^ j
      ≤ ∑ j ∈ range (k + 1), (R : ℝ) ^ j * 2 ^ j := by
        apply sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.choose_le_pow R j
    _ = ∑ j ∈ range (k + 1), (2 * (R : ℝ)) ^ j := by
        apply sum_congr rfl
        intro j _
        rw [mul_pow, mul_comm]
    _ ≤ (2 * (R : ℝ)) ^ (k + 1) := hgeom k

/-- Brun display 9 adapted to the indexed Goldbach polynomial. -/
theorem r_le_brun9 (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hP0 : P.Nonempty) (k : ℕ) (hk : Even k) :
    let S : ℝ := ∑ p ∈ P, S1.wt n p / p
    (r n : ℝ) ≤ n * Real.exp (-S) + n * (3 * S / (k + 1 : ℕ)) ^ (k + 1) +
      (2 * (P.card : ℝ)) ^ (k + 1) + 2 * P.card := by
  dsimp only
  have hS : 0 ≤ ∑ p ∈ P, S1.wt n p / p :=
    sum_nonneg fun p _ => div_nonneg (S1.wt_pos n p).le (Nat.cast_nonneg p)
  have h := r_le_pure_brun n P hP k hk
  have h1 := mul_le_mul_of_nonneg_left (product_le_exp n P hP) (Nat.cast_nonneg n)
  have h2 := mul_le_mul_of_nonneg_left
    (factorial_tail_le _ hS (k + 1) (Nat.succ_pos k)) (Nat.cast_nonneg n)
  have h3 := binomial_remainder_le P.card k (card_pos.mpr hP0)
  linarith

end LeanLab.SchnirelmannGoldbach.PureSieve

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.factorial_ge_third_power

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.factorial_tail_le

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.binomial_remainder_le

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.r_le_brun9
