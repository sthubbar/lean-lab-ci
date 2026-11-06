/-
AI wrote this Lean code. Binary Goldbach is open.
Pintz and Ruzsa 2003 pages 176 to 177, scalar bounds for Lemma 4.
-/
import Mathlib

namespace LeanLab.PlattTrudgian2014

/-- P0026 page 176 display 4.16, an elementary central binomial estimate. -/
theorem central_binomial_square380 (n : ℕ) :
    ((4 : ℝ) ^ n) ^ 2 ≤ (4 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hr : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
        2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hr2 := congrArg (fun x : ℝ => (4 * (n : ℝ) + 5) * x ^ 2) hr
    have hn : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    apply (mul_le_mul_iff_right₀ hn).mp
    push_cast
    rw [show (4 : ℝ) ^ (n + 1) = 4 ^ n * 4 from pow_succ _ _]
    nlinarith [mul_le_mul_of_nonneg_left ih (by positivity :
      (0 : ℝ) ≤ 16 * ((n : ℝ) + 1) ^ 2), sq_nonneg (Nat.centralBinom n : ℝ)]

/-- P0026 page 176 display 4.16, a concrete square root loss. -/
theorem central_binomial_sqrt380 (n : ℕ) :
    (4 : ℝ) ^ n ≤ 2 * Real.sqrt ((n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
  have hs := central_binomial_square380 n
  have hc : (0 : ℝ) ≤ Nat.centralBinom n := Nat.cast_nonneg _
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
  have hsqmul := congrArg (fun x : ℝ => 4 * x * (Nat.centralBinom n : ℝ) ^ 2) hsq
  have hp : (0 : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by positivity
  nlinarith [sq_nonneg (Nat.centralBinom n : ℝ)]

/-- P0026 page 177, the cutoff used after display 4.17 has square root size. -/
theorem cutoff_sqrt380 (A : ℝ) (hA : 0 ≤ A) :
    Real.sqrt ((2 * ⌊A⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.sqrt A) := by
  have hf := Nat.floor_le hA
  have hs := Real.sq_sqrt hA
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · push_cast
    nlinarith [Real.sqrt_nonneg A]

/-- P0026 page 175, the supermultiplicative argument following display 4.12.
A uniform exponential envelope loses its constant at each fixed length. -/
theorem supermultiplicative_remove_prefactor380 (u : ℕ → ℝ) (C p : ℝ)
    (hzero : u 0 = 1) (hnonneg : ∀ n, 0 ≤ u n)
    (hprod : ∀ m n, u m * u n ≤ u (m + n))
    (hbound : ∀ n, u n ≤ C * Real.exp (p * n)) (L : ℕ) :
    u L ≤ Real.exp (p * L) := by
  have hpow (n : ℕ) : u L ^ n ≤ u (n * L) := by
    induction n with
    | zero => simp [hzero]
    | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact (mul_le_mul_of_nonneg_right ih (hnonneg L)).trans (hprod _ _)
  by_contra h
  have hq : 1 < u L / Real.exp (p * L) :=
    (one_lt_div (Real.exp_pos _)).mpr (lt_of_not_ge h)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hq
  have hle : (u L / Real.exp (p * L)) ^ n ≤ C := by
    rw [div_pow, div_le_iff₀ (pow_pos (Real.exp_pos _) n)]
    calc
      _ ≤ u (n * L) := hpow n
      _ ≤ C * Real.exp (p * (n * L : ℕ)) := hbound _
      _ = C * Real.exp (p * L) ^ n := by
        rw [← Real.exp_nat_mul]
        push_cast
        congr 2
        ring
  exact (not_lt_of_ge hle) hn

#print axioms central_binomial_square380
#print axioms central_binomial_sqrt380
#print axioms cutoff_sqrt380
#print axioms supermultiplicative_remove_prefactor380

end LeanLab.PlattTrudgian2014
