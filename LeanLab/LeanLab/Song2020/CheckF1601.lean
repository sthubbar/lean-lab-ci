import LeanLab.Song2020.State1562

open LeanLab.Song2020

example (N0 : ℕ) :
    ((3 ^ (65 + N0) : ℕ) : ℝ) ^ (63 / 64 : ℝ) = ((3 ^ (63 * (65 + N0)) : ℕ) : ℝ) := by
  rw [show (63 / 64 : ℝ) = (64 : ℝ)⁻¹ * 63 by norm_num,
    Real.rpow_mul_natCast (by positivity) (64 : ℝ)⁻¹ 63]
  rw [← Real.rpow_natCast]
  rw [← Nat.cast_pow]
  rw [Real.pow_rpow_inv_natCast (x := (3 : ℝ)) (by norm_num) (by norm_num)]
  congr 1
  ring

example (N0 : ℕ) :
    ((3 ^ (65 + N0) : ℕ) : ℝ) ^ (63 / 64 : ℝ) < ((3 ^ (65 + N0) : ℕ) : ℝ) / 3 := by
  rw [show (63 / 64 : ℝ) = (64 : ℝ)⁻¹ * 63 by norm_num,
    Real.rpow_mul_natCast (by positivity) (64 : ℝ)⁻¹ 63]
  rw [← Real.rpow_natCast]
  rw [← Nat.cast_pow]
  rw [Real.pow_rpow_inv_natCast (x := (3 : ℝ)) (by norm_num) (by norm_num)]
  have hexp : 63 * (65 + N0) < 64 * (65 + N0) := by omega
  have hpow : (3 ^ (63 * (65 + N0)) : ℕ) < 3 ^ (64 * (65 + N0)) :=
    Nat.pow_lt_pow_left (by omega) hexp
  have hpowR : ((3 ^ (63 * (65 + N0)) : ℕ) : ℝ) <
      ((3 ^ (64 * (65 + N0)) : ℕ) : ℝ) := by exact_mod_cast hpow
  rw [show ((3 ^ (64 * (65 + N0)) : ℕ) : ℝ) =
      ((3 ^ (65 + N0) : ℕ) : ℝ) / 3 by
      rw [← Nat.cast_pow]
      rw [Nat.cast_mul, Nat.cast_ofNat]
      simp [Nat.succ_eq_add_one, Nat.cast_add]
      ring]
  exact hpowR
