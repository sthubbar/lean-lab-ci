/-
Explicit size bounds for the omitted higher prime powers.
Source: P0029 page 4 and the representation inference on page 13.
All constants and thresholds here are derived, not printed paper constants.
The sealed DecompJ1034 statements stay unchanged.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp384b
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LeanLab.BhowmikGrimmelt2026

/-- The corrected square root bound with coefficient three halves for N at least sixteen.
Source: a derived bound for the omission on P0029 page 4.
The real exponent is explicit and differs from the sealed natural exponent zero. -/
theorem prime_power_error_three_halves384 (N : ℕ) (hN : 16 ≤ N) :
    r2 N - primeR2_384 N ≤ 3 / 2 * (N : ℝ) ^ ((1 : ℝ) / 2) * (Real.log N) ^ 3 := by
  have hlog16 : (8 / 3 : ℝ) ≤ Real.log (16 : ℝ) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    linarith [Real.log_two_gt_d9]
  have hlog : (8 / 3 : ℝ) ≤ Real.log (N : ℝ) :=
    hlog16.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have hbudget := r2_sub_primeR2_sqrt_log_sq384 N (by omega)
  rw [Real.sqrt_eq_rpow] at hbudget
  calc
    _ ≤ 4 * (N : ℝ) ^ ((1 : ℝ) / 2) * (Real.log N) ^ 2 := hbudget
    _ ≤ _ := by
      have hsq : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * (Real.log N) ^ 2 := by positivity
      nlinarith [mul_nonneg hsq (show 0 ≤ 3 / 2 * Real.log (N : ℝ) - 4 by linarith)]

/-- An explicit logarithm bound above two to the twenty fourth.
Source: a derived growth comparison for P0029 page 4, using log_div_self_rpow_antitoneOn. -/
theorem log_le_quarter_power384 (N : ℕ) (hN : 2 ^ 24 ≤ N) :
    Real.log (N : ℝ) ≤ 17 / 64 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
  have hbasepos : (0 : ℝ) < ((2 ^ 24 : ℕ) : ℝ) := by positivity
  have hlogbase : Real.log (((2 ^ 24 : ℕ) : ℝ)) = 24 * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    norm_num
  have hbaseexp : Real.exp ((1 / 4 : ℝ)⁻¹) ≤ ((2 ^ 24 : ℕ) : ℝ) := by
    apply (Real.le_log_iff_exp_le hbasepos).mp
    rw [hlogbase]
    norm_num
    linarith [Real.log_two_gt_d9]
  have hNR : ((2 ^ 24 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmono := Real.log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 1 / 4)
    hbaseexp (hbaseexp.trans hNR) hNR
  have hroot : (((2 ^ 24 : ℕ) : ℝ)) ^ ((1 : ℝ) / 4) = 64 := by
    rw [show (((2 ^ 24 : ℕ) : ℝ)) = (64 : ℝ) ^ 4 by norm_num]
    simpa only [one_div, Nat.cast_ofNat] using Real.pow_rpow_inv_natCast (x := (64 : ℝ))
      (n := 4) (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
  dsimp only at hmono
  rw [hroot, hlogbase] at hmono
  have hb : 24 * Real.log 2 / 64 ≤ (17 / 64 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  have hpos : 0 < (N : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  exact (div_le_iff₀ hpos).mp (hmono.trans hb)

/-- The explicit prime power budget is at most N divided by three above two to the twenty fourth.
Source: a derived numerical estimate for P0029 pages 4 and 13. -/
theorem prime_power_budget_le_third384 (N : ℕ) (hN : 2 ^ 24 ≤ N) :
    4 * Real.sqrt N * (Real.log N) ^ 2 ≤ (N : ℝ) / 3 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlog := pow_le_pow_left₀ hlog0 (log_le_quarter_power384 N hN) 2
  have hroot : ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt N := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 4)) 2,
      ← Real.rpow_mul (Nat.cast_nonneg N), Real.sqrt_eq_rpow]
    norm_num
  rw [mul_pow, hroot] at hlog
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt N = (N : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg N)
  have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4 * Real.sqrt (N : ℝ) by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The full higher prime power error is at most N divided by three on the explicit range.
Source: derived prime power removal for P0029 page 13. -/
theorem prime_power_error_le_third384 (N : ℕ) (hN : 2 ^ 24 ≤ N) :
    r2 N - primeR2_384 N ≤ (N : ℝ) / 3 :=
  (r2_sub_primeR2_sqrt_log_sq384 N (by omega)).trans
    (prime_power_budget_le_third384 N hN)

/-- The main term is controlled by the absolute representation error and the actual prime count.
Source: the error comparison on P0029 page 13, with the prime power error retained.
No singular lower bound or exception hypothesis is assumed. -/
theorem representation_error_comparison384 (N : ℕ) (hN : 2 ^ 24 ≤ N) :
    (singular N - 1 / 3) * N ≤ |E2 N| + primeR2_384 N := by
  have hr := prime_power_error_le_third384 N hN
  have hE := neg_le_abs (E2 N)
  unfold E2 at hE ⊢
  nlinarith

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.prime_power_error_three_halves384
#print axioms LeanLab.BhowmikGrimmelt2026.log_le_quarter_power384
#print axioms LeanLab.BhowmikGrimmelt2026.prime_power_budget_le_third384
#print axioms LeanLab.BhowmikGrimmelt2026.prime_power_error_le_third384
#print axioms LeanLab.BhowmikGrimmelt2026.representation_error_comparison384
