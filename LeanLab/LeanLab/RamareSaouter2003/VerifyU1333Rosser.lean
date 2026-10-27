/- VERIFY U-1333 scratch, run 20261021T0203Z-29730: verbatim copy of log_two_pi_le, log_thousand_ge,
rosser_err_le from Lemma1Rosser.lean, importing Mathlib only, because MuStar55Cert, which Lemma1Rosser
imports, needs about 13 GB and this machine has 8 GB. AI-written. -/
import Mathlib
namespace LeanLab.RamareSaouter2003.VerifyU1333
open Real
theorem log_two_pi_le : Real.log (2 * π) ≤ 1.838 := by
  have p2 := Real.pi_lt_d6
  have e2 := Real.exp_one_lt_d9
  have l2 := Real.log_two_lt_d9
  have hE3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have hz0 : 0 < 2 * π * Real.exp 3 / 2 ^ 7 := by positivity
  have hsplit : Real.log (2 * π) = 7 * Real.log 2 - 3 + Real.log (2 * π * Real.exp 3 / 2 ^ 7) := by
    have h : Real.log (2 * π * Real.exp 3 / 2 ^ 7) = Real.log (2 * π) + 3 - 7 * Real.log 2 := by
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (x := 2 * π) (by positivity) (by positivity), Real.log_exp, Real.log_pow]
      push_cast; ring
    rw [h]; ring
  have h1 := Real.log_le_sub_one_of_pos hz0
  have h3 : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by
    gcongr
  have hz : 2 * π * Real.exp 3 / 2 ^ 7 ≤ 2 * 3.141593 * (2.7182818286 : ℝ) ^ 3 / 2 ^ 7 := by
    rw [hE3]; gcongr
  have hn : 2 * 3.141593 * (2.7182818286 : ℝ) ^ 3 / 2 ^ 7 ≤ 0.98595 := by norm_num
  linarith

/-- log 1000 ≥ 6.9074, from 1000 = 2^10 (1000/1024). PROVED. -/
theorem log_thousand_ge : 6.9074 ≤ Real.log 1000 := by
  have l1 := Real.log_two_gt_d9
  have hsplit : Real.log 1000 = 10 * Real.log 2 + Real.log (1000 / 2 ^ 10) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1000 / 2 ^ 10 by norm_num)
  have : (1 : ℝ) - (1000 / 2 ^ 10)⁻¹ = -0.024 := by norm_num
  linarith

/-- The numerical heart of Lemma 1: Rosser's error is at most 0.67 log(T/2π) for T ≥ 10^3. PROVED. -/
theorem rosser_err_le (T : ℝ) (hT : 1000 ≤ T) :
    0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + 0.2 / T ≤
      0.67 * Real.log (T / (2 * π)) := by
  have hT0 : 0 < T := by linarith
  set x := Real.log T with hx
  have hx0 : 6.9074 ≤ x := le_trans log_thousand_ge (Real.log_le_log (by norm_num) hT)
  have hxpos : 0 < x := by linarith
  -- log x ≤ 1 + x / e^2
  have he2 : (7.389 : ℝ) ≤ Real.exp 2 := by
    have e1 := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; nlinarith
  have hE : 0 < Real.exp 2 := Real.exp_pos _
  have hlx : Real.log x ≤ 1 + x / 7.389 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hxpos hE)
    rw [Real.log_div hxpos.ne' hE.ne', Real.log_exp] at h1
    have : x / Real.exp 2 ≤ x / 7.389 := by gcongr
    linarith
  have hlog : Real.log (T / (2 * π)) = x - Real.log (2 * π) := by
    rw [Real.log_div hT0.ne' (by positivity)]
  have h2π := log_two_pi_le
  have hTinv : 0.2 / T ≤ 0.0002 := by
    rw [div_le_iff₀ hT0]; nlinarith
  rw [hlog]
  norm_num at hx0 hlx h2π hTinv ⊢
  linarith

end LeanLab.RamareSaouter2003.VerifyU1333
#print axioms LeanLab.RamareSaouter2003.VerifyU1333.rosser_err_le
