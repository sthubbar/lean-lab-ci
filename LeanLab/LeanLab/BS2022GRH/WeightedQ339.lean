/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Weighted qG monotonicity needed for the inverse powers in display 31.
Journal qG formula p. 1216 and mbar comparison p. 1240.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Mphi339

namespace LeanLab.BS2022GRH.WeightedQ339
open Real Finset Classical ChenThresholdGRH
noncomputable section

/-- The printed qG coefficient multiplied by square root x times log x,
written at x equal to exp t. Journal p. 1216. -/
def weightedQLog (t : ℝ) : ℝ :=
  0.165 * exp (t / 2) * t + 12.683 * exp (t / 2) +
    254.980 * (exp (t / 2) / t) + 2607.854 * (exp (t / 2) / t ^ 2) +
    11605.056 * (exp (t / 2) / t ^ 3) +
    (1.314 * t + 0.092 * log t + 60.883) * exp (t / 4) * t +
    8.250 * log t * exp (t / 4) + 939.260 * exp (t / 4) - 237.934

/-- The three reciprocal powers in the weighted qG formula increase past six.
Use the existing logarithmic monotonicity theorem, journal p. 1216. -/
theorem exp_half_div_pow_mono (k : ℕ) (s t : ℝ) (hk : 1 ≤ k) (hk3 : k ≤ 3)
    (hs : 6 ≤ s) (hst : s ≤ t) : exp (s / 2) / s ^ k ≤ exp (t / 2) / t ^ k := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk3R : (k : ℝ) ≤ 3 := by exact_mod_cast hk3
  have hm := Journal.mono_step (by norm_num : (0 : ℝ) < 1 / 2)
    (by linarith : (0 : ℝ) < k) (by linarith : (k : ℝ) / (1 / 2) ≤ s) hst
  have hid (v : ℝ) (hv : 0 < v) :
      exp (v / 2) / v ^ k = exp ((1 / 2 : ℝ) * v - (k : ℝ) * log v) := by
    rw [exp_sub, exp_nat_mul, exp_log hv]
    congr 2 <;> ring
  rw [hid s hs0, hid t ht0]
  exact exp_le_exp.mpr hm

/-- Exact regrouping of the printed qG formula after multiplying its standard scale.
The negative term becomes a constant, journal p. 1216. -/
theorem weighted_identity (t : ℝ) (ht : 0 < t) :
    qG (exp t) * √(exp t) * t = weightedQLog t := by
  have hs : √(exp t) = exp (t / 2) := by
    rw [sqrt_eq_rpow, ← exp_mul]
    congr 1
    ring
  have he : exp (t / 2) = exp (t / 4) ^ (2 : ℕ) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  rw [DecompC164a.qG_groups (exp t) (exp_pos t), hs]
  simp only [log_exp]
  unfold DecompC164a.firstGroup DecompC164a.secondGroup DecompC164a.thirdGroup weightedQLog
  simp only [he]
  field_simp [ht.ne', exp_ne_zero (t / 4)] <;> ring

/-- The weighted logarithmic formula increases for t at least six.
Every nonconstant term is nonnegative and increasing on this domain, p. 1216. -/
theorem weighted_log_monotone (s t : ℝ) (hs : 6 ≤ s) (hst : s ≤ t) :
    weightedQLog s ≤ weightedQLog t := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hls : 0 ≤ log s := log_nonneg (by linarith)
  have hlt : 0 ≤ log t := log_nonneg (by linarith)
  have hlog := log_le_log hs0 hst
  have h1 : 0.165 * exp (s / 2) * s ≤ 0.165 * exp (t / 2) * t := by gcongr
  have h2 : 12.683 * exp (s / 2) ≤ 12.683 * exp (t / 2) := by gcongr
  have h3 : 254.980 * (exp (s / 2) / s) ≤ 254.980 * (exp (t / 2) / t) := by
    simpa only [pow_one] using mul_le_mul_of_nonneg_left
      (exp_half_div_pow_mono 1 s t (by norm_num) (by norm_num) hs hst) (by norm_num : (0 : ℝ) ≤ 254.980)
  have h4 : 2607.854 * (exp (s / 2) / s ^ 2) ≤ 2607.854 * (exp (t / 2) / t ^ 2) :=
    mul_le_mul_of_nonneg_left (exp_half_div_pow_mono 2 s t (by norm_num) (by norm_num) hs hst)
      (by norm_num)
  have h5 : 11605.056 * (exp (s / 2) / s ^ 3) ≤ 11605.056 * (exp (t / 2) / t ^ 3) :=
    mul_le_mul_of_nonneg_left (exp_half_div_pow_mono 3 s t (by norm_num) (by norm_num) hs hst)
      (by norm_num)
  have h6 : (1.314 * s + 0.092 * log s + 60.883) * exp (s / 4) * s ≤
      (1.314 * t + 0.092 * log t + 60.883) * exp (t / 4) * t := by gcongr
  have h7 : 8.250 * log s * exp (s / 4) ≤ 8.250 * log t * exp (t / 4) := by gcongr
  have h8 : 939.260 * exp (s / 4) ≤ 939.260 * exp (t / 4) := by gcongr
  unfold weightedQLog
  linarith only [h1, h2, h3, h4, h5, h6, h7, h8]

/-- qG times square root x times log x increases once log x is at least six.
This is the scaled error function of the printed Lemma 3, p. 1216. -/
theorem weighted_q_monotone (x y : ℝ) (hx : 0 < x) (hL : 6 ≤ log x) (hxy : x ≤ y) :
    qG x * √x * log x ≤ qG y * √y * log y := by
  have hy : 0 < y := hx.trans_le hxy
  have hlog := log_le_log hx hxy
  have hm := weighted_log_monotone (log x) (log y) hL hlog
  rw [← weighted_identity (log x) (by linarith), ← weighted_identity (log y) (by linarith)] at hm
  simpa only [exp_log hx, exp_log hy] using hm

/-- qG at twice w times w times log w increases on the large slice range.
This is the product controlling the inverse qG powers in display 31, p. 1240. -/
theorem qG_mul_log_monotone (W T : ℝ) (hW : 0 < W) (hL : 2750 ≤ log W) (hWT : W ≤ T) :
    qG (2 * W) * W * log W ≤ qG (2 * T) * T * log T := by
  have hT : 0 < T := hW.trans_le hWT
  have hlW : 0 < log W := by linarith
  have hlog := log_le_log hW hWT
  have hlT : 0 < log T := hlW.trans_le hlog
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hs2 : 0 < √(2 : ℝ) := by positivity
  have hW25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hqT := DecompC164b.qG_positive (2 * T) (by linarith)
  have hl2T : 0 < log (2 * T) := log_pos (by linarith)
  let R : ℝ → ℝ := fun v => √v / √2 * (log v / (log 2 + log v))
  have hratio : log W / (log 2 + log W) ≤ log T / (log 2 + log T) := by
    apply (div_le_div_iff₀ (add_pos hl2 hlW) (add_pos hl2 hlT)).mpr
    have hp := mul_nonneg hl2.le (sub_nonneg.mpr hlog)
    nlinarith only [hp]
  have hR : R W ≤ R T := by
    apply mul_le_mul (div_le_div_of_nonneg_right (sqrt_le_sqrt hWT) hs2.le) hratio
    · exact div_nonneg hlW.le (add_pos hl2 hlW).le
    · positivity
  have hF := weighted_q_monotone (2 * W) (2 * T) (by positivity)
    (by rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hW.ne']; linarith) (by gcongr)
  have hprod := mul_le_mul hF hR (by dsimp [R]; positivity)
    (by positivity : 0 ≤ qG (2 * T) * √(2 * T) * log (2 * T))
  have hid (v : ℝ) (hv : 0 < v) (hlv : 0 < log v) :
      (qG (2 * v) * √(2 * v) * log (2 * v)) * R v = qG (2 * v) * v * log v := by
    dsimp [R]
    rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), log_mul (by norm_num : (2 : ℝ) ≠ 0) hv.ne']
    field_simp [hs2.ne', (add_pos hl2 hlv).ne']
    <;> ring_nf
    <;> simp only [sq_sqrt hv.le]
    <;> ring
  rw [hid W hW hlW, hid T hT hlT] at hprod
  exact hprod

end
end LeanLab.BS2022GRH.WeightedQ339
#print axioms LeanLab.BS2022GRH.WeightedQ339.exp_half_div_pow_mono
#print axioms LeanLab.BS2022GRH.WeightedQ339.weighted_identity
#print axioms LeanLab.BS2022GRH.WeightedQ339.weighted_log_monotone
#print axioms LeanLab.BS2022GRH.WeightedQ339.weighted_q_monotone
#print axioms LeanLab.BS2022GRH.WeightedQ339.qG_mul_log_monotone
