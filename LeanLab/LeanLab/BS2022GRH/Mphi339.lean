/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Monotonicity of the scalar Mphi factors in display 31.
Journal pp. 1239 and 1240.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Scalar339

namespace LeanLab.BS2022GRH.Mphi339
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- Mphi decreases above one, as used after display 32 on journal p. 1240. -/
theorem Mphi_antitone (x y : ℝ) (hx : 1 < x) (hxy : x ≤ y) : Mphi y ≤ Mphi x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlx : 0 < log x := log_pos hx
  have hly : 0 < log y := log_pos (hx.trans_le hxy)
  have hlog := log_le_log hx0 hxy
  have hsqrt := sqrt_le_sqrt hxy
  have hsx : 0 < √x := sqrt_pos.mpr hx0
  have h1 : 1.333 / log y ≤ (1.333 : ℝ) / log x :=
    div_le_div_of_nonneg_left (by norm_num) hlx hlog
  have h2 : 2.44 / (√y * log y) ≤ (2.44 : ℝ) / (√x * log x) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul hsqrt hlog hlx.le (sqrt_nonneg _)
  have h3 : 11 / (√y * log y ^ 2) ≤ (11 : ℝ) / (√x * log x ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
  exact add_le_add (add_le_add (le_rfl : (1 : ℝ) ≤ 1) h1) (min_le_min h2 h3)

/-- The Lemma 8 cube root cutoff increases on its full numerical domain.
Use Mathlib log_div_sqrt_antitoneOn and the existing qG antitone theorem.
Journal p. 1239 coefficient comparison before display 31. -/
theorem cutoff_monotone (Y T : ℝ) (hY : 25 ≤ Y) (hYT : Y ≤ T) : cutoff Y ≤ cutoff T := by
  have hY0 : 0 < Y := by linarith
  have hT0 : 0 < T := by linarith
  have hlogY : 0 < log Y := log_pos (by linarith)
  have hlogT : 0 < log T := log_pos (by linarith)
  have hsY : 0 < √Y := sqrt_pos.mpr hY0
  have hsT : 0 < √T := sqrt_pos.mpr hT0
  have hqY := DecompC164b.qG_positive Y hY
  have hqT := DecompC164b.qG_positive T (hY.trans hYT)
  have hq := DecompC164a.qG_antitone Y T (by linarith) hYT
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have he2 : exp (2 : ℝ) ≤ 9 := by
    have heq : exp (2 : ℝ) = exp (1 : ℝ) ^ (2 : ℕ) := by rw [← exp_nat_mul]; norm_num
    rw [heq]
    nlinarith [exp_one_lt_d9, exp_pos (1 : ℝ)]
  have hmono := log_div_sqrt_antitoneOn (he2.trans (by linarith : (9 : ℝ) ≤ Y))
    (he2.trans (by linarith : (9 : ℝ) ≤ T)) hYT
  have hcross := (div_le_div_iff₀ hsT hsY).mp hmono
  have hratio : √Y / log Y ≤ √T / log T :=
    (div_le_div_iff₀ hlogY hlogT).mpr (by nlinarith only [hcross])
  have hden : 2 * log 2 * qG T ≤ 2 * log 2 * qG Y :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have hid (v : ℝ) : √v / (2 * log 2 * qG v * log v) =
      (√v / log v) / (2 * log 2 * qG v) := by
    rw [div_div]
    congr 1
    ring
  unfold cutoff
  apply rpow_le_rpow (by positivity) _ (by norm_num)
  rw [hid Y, hid T]
  exact div_le_div₀ (by positivity) hratio (by positivity) hden

/-- Mphi0 decreases whenever the lower cube root cutoff exceeds one.
Journal p. 1239 comparison of the normalized Lemma 8 coefficient. -/
theorem Mphi0_antitone (Y T : ℝ) (hY : 25 ≤ Y) (hYT : Y ≤ T) (hcut : 1 < cutoff Y) :
    Mphi0 T ≤ Mphi0 Y := by
  exact Mphi_antitone (cutoff Y) (cutoff T) hcut (cutoff_monotone Y T hY hYT)

/-- At the source slice size the cube root cutoff exceeds one without a GRH input.
This proves that Mphi0 uses the decreasing positive branch of Mphi.
Journal pp. 1239 and 1240. -/
theorem cutoff_gt_one_large (Y : ℝ) (hY0 : 0 < Y) (hL : 2750 ≤ log Y) : 1 < cutoff Y := by
  have hlogY : 0 < log Y := by linarith
  have hY : 25 ≤ Y := by linarith [log_le_sub_one_of_pos hY0]
  have hq0 := DecompC164b.qG_positive Y hY
  have hq := Scalar339.qG_upper Y hY0 hL
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog21 : log (2 : ℝ) ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hs : 0 < √Y := sqrt_pos.mpr hY0
  have hls := log_le_sub_one_of_pos hs
  rw [log_sqrt hY0.le] at hls
  have hden0 : 0 < 2 * log 2 * qG Y * log Y := by positivity
  have hden : 2 * log 2 * qG Y * log Y ≤ 0.34 * log Y := by
    calc _ ≤ 2 * 1 * 0.17 * log Y := by gcongr
      _ = _ := by ring
  have hsmall : 2 * log 2 * qG Y * log Y < √Y := by nlinarith
  unfold cutoff
  exact one_lt_rpow ((one_lt_div hden0).mpr hsmall) (by norm_num)

/-- Mphi0 is at least one throughout the large slice domain.
Journal p. 1239 display 31. -/
theorem one_le_Mphi0 (Y : ℝ) (hY0 : 0 < Y) (hL : 2750 ≤ log Y) : 1 ≤ Mphi0 Y := by
  exact Lemma5Coeffs138.one_le_Mphi (cutoff Y) (cutoff_gt_one_large Y hY0 hL)

end
end LeanLab.BS2022GRH.Mphi339
#print axioms LeanLab.BS2022GRH.Mphi339.Mphi_antitone
#print axioms LeanLab.BS2022GRH.Mphi339.cutoff_monotone
#print axioms LeanLab.BS2022GRH.Mphi339.Mphi0_antitone
#print axioms LeanLab.BS2022GRH.Mphi339.cutoff_gt_one_large
#print axioms LeanLab.BS2022GRH.Mphi339.one_le_Mphi0
