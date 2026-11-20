import LeanLab.Ported.Prove2Me.LL_Decomp368b_primorial_c4

/-!
Stronger derived endpoint certificates for the three open initial states.
Source Schoenfeld 1976 page 356 display 5.1 star, derived finite obligations.
The logarithm margin pays for the existing checkpoint scale two to power 4096.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task664
open LeanLab.Ported.Prove2Me.Task664
open ThetaSieve PrimC3Cert

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A stronger theta inequality pays for the fixed checkpoint scale. -/
theorem scaled_of_theta (n : ℕ) (hn : 6000000 ≤ n)
    (h : (Q : ℝ) * th n < (n : ℝ) * (18449176835997853236 : ℕ)) :
    primorial n * 25 ^ n * 2 ^ 4096 < 68 ^ n := by
  have hq : (Q : ℝ) = 18446744073709551616 := by norm_num [Q]
  have hc := c_le cpos
  rw [cval] at hc
  have hc' : (18449176835997853236 : ℝ) ≤
      (Q : ℝ) * (Real.log (68 / 25) - 1 / 2000) := by
    rw [hq] at hc ⊢
    norm_num only [Nat.cast_ofNat] at hc
    linarith
  have hnr : (6000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hscaled : (Q : ℝ) * th n < Q * ((n : ℝ) * (Real.log (68 / 25) - 1 / 2000)) := by
    calc
      (Q : ℝ) * th n < (n : ℝ) * (18449176835997853236 : ℕ) := h
      _ ≤ (n : ℝ) * (Q * (Real.log (68 / 25) - 1 / 2000)) :=
        mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg n)
      _ = _ := by ring
  have ht : th n < (n : ℝ) * (Real.log (68 / 25) - 1 / 2000) :=
    lt_of_mul_lt_mul_left hscaled Q_pos.le
  have hm : (4096 : ℝ) * Real.log 2 ≤ (n : ℝ) / 2000 := by
    nlinarith [Real.log_two_lt_d9]
  have ht' : th n + 4096 * Real.log 2 < (n : ℝ) * Real.log (68 / 25) := by
    nlinarith
  have hth : th n = Real.log (primorial n) := by
    unfold th
    rw [Chebyshev.theta_eq_log_primorial]
    simp
  rw [hth, Real.log_div (by norm_num) (by norm_num)] at ht'
  have hp : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have key : Real.log ((primorial n : ℝ) * 25 ^ n * 2 ^ 4096) <
      Real.log ((68 : ℝ) ^ n) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul hp.ne' (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hreal := (Real.log_lt_log_iff (by positivity) (by positivity)).1 key
  exact_mod_cast hreal

/-- The direct stronger checker covers the integer endpoint six million. -/
theorem scaled6_certificate :
    primChain 18449176835997853236 5999999 128 256 32 3932163
      72501911950632556508439696 = true := by
  decide +kernel

/-- The direct stronger checker covers the integer endpoint eight million. -/
theorem scaled8_certificate :
    primChain 18449176835997853236 7999999 128 256 63 3932163
      72501911950632556508439696 = true := by
  decide +kernel

/-- The direct stronger checker covers the integer endpoint twelve million. -/
theorem scaled12_certificate :
    primChain 18449176835997853236 11999999 128 256 62 7995395
      147436398244268766209164068 = true := by
  decide +kernel

/-- The exact scaled initial state at six million, with a strict margin. -/
theorem checkpoint_6m :
    primorial 6000000 * 25 ^ 6000000 * 2 ^ 4096 < 68 ^ 6000000 := by
  apply scaled_of_theta _ (by omega)
  exact primChain_sound 32 3932163 72501911950632556508439696
    scaled6_certificate hiInv_3932163 6000000 (by omega) (by omega) (by omega)

/-- The exact scaled initial state at eight million, with a strict margin. -/
theorem checkpoint_8m :
    primorial 8000000 * 25 ^ 8000000 * 2 ^ 4096 < 68 ^ 8000000 := by
  apply scaled_of_theta _ (by omega)
  exact primChain_sound 63 3932163 72501911950632556508439696
    scaled8_certificate hiInv_3932163 8000000 (by omega) (by omega) (by omega)

/-- The exact scaled initial state at twelve million, with a strict margin. -/
theorem checkpoint_12m :
    primorial 12000000 * 25 ^ 12000000 * 2 ^ 4096 < 68 ^ 12000000 := by
  apply scaled_of_theta _ (by omega)
  exact primChain_sound 62 7995395 147436398244268766209164068
    scaled12_certificate PrimC4Cert.hiInv_7995395 12000000 (by omega) (by omega) (by omega)

end LeanLab.LiuWang2002.Task664
#print axioms LeanLab.LiuWang2002.Task664.scaled_of_theta
#print axioms LeanLab.LiuWang2002.Task664.scaled6_certificate
#print axioms LeanLab.LiuWang2002.Task664.scaled8_certificate
#print axioms LeanLab.LiuWang2002.Task664.scaled12_certificate
#print axioms LeanLab.LiuWang2002.Task664.checkpoint_6m
#print axioms LeanLab.LiuWang2002.Task664.checkpoint_8m
#print axioms LeanLab.LiuWang2002.Task664.checkpoint_12m
