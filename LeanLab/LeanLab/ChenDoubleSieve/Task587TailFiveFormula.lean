import LeanLab.ChenDoubleSieve.Task587Tail

/-!
Scalar delay formulas for Wu 2004 Lemma 2.10 page 9.
Source: https://arxiv.org/abs/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set Finset MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional Wu04Buchstab

/-- The delay equation has an exact scalar formula on the next unit interval.
Wu 2004 Lemma 2.10 page 9, derived by integration. -/
theorem buchstab_three_four_formula {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Set.Icc 3 4) : u * ω u = 1 + log (u - 1) + J 2 (u - 1) := by
  have hu3 := hu.1
  have hu4 := hu.2
  have hc : ContinuousOn (fun t : ℝ => t * ω t) (Set.Icc 3 u) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc 3 u) := by
    rw [uIcc_of_le hu.1]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1]
  have hf := integral_eq_sub_of_hasDerivAt_of_le hu.1 hc
    (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
  have he : (∫ t in (3 : ℝ)..u, ω (t - 1)) =
      ∫ t in (2 : ℝ)..(u - 1), (1 + log (t - 1)) / t := by
    rw [integral_comp_sub_right ω]
    norm_num
    apply integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith : (2 : ℝ) ≤ u - 1)] at ht
    exact formula_two_three hω ⟨ht.1, by linarith [ht.2, hu.2]⟩
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / t) volume 2 (u - 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    rw [uIcc_of_le (by linarith : (2 : ℝ) ≤ u - 1)] at ht
    exact (show 0 < t from lt_of_lt_of_le (by norm_num) ht.1).ne'
  have hi2 := Wu04Panels.J_integrable (by norm_num : (1 : ℝ) < 2)
    (by linarith : (2 : ℝ) ≤ u - 1)
  have hj : (∫ t in (2 : ℝ)..(u - 1), (1 + log (t - 1)) / t) =
      log (u - 1) - log 2 + J 2 (u - 1) := by
    simp_rw [add_div]
    rw [intervalIntegral.integral_add hi1 hi2]
    simp only [one_div, integral_inv_of_pos (by norm_num : (0 : ℝ) < 2)
      (by linarith : (0 : ℝ) < u - 1), J]
    rw [log_div (by linarith : u - 1 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  have h3 := formula_two_three hω (u := 3) (by norm_num)
  norm_num at h3
  rw [he, hj] at hf
  linarith

/-- J is increasing once both endpoints are at least two.
Wu 2004 page 26, derived monotonicity of the nonnegative scalar kernel. -/
theorem J_mono_after_two {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) : J 2 a ≤ J 2 b := by
  apply intervalIntegral.integral_mono_interval le_rfl ha hab
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (log_nonneg (by linarith [ht.1])) (by linarith [ht.1])
  · exact Wu04Panels.J_integrable (by norm_num) (ha.trans hab)

/-- A finer scalar endpoint certificate at three.
Wu 2004 page 26, derived exact rational panel bound. -/
theorem J_three_fine_certificate : Burst9Psi2.jUpperSum 3 128 ≤ (1473 / 10000 : ℚ) := by
  decide +kernel

/-- A finer bound at four prepares the next delay step.
Wu 2004 Lemma 2.10 page 9, derived exact enclosure. -/
theorem buchstab_four_le_5615 {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ω 4 ≤ (5615 / 10000 : ℝ) := by
  have hj := Burst9Psi2.J_upper_of_cert (by norm_num) (by norm_num) J_three_fine_certificate
  have hl := (Wu04Integral.log_bounds 12 (y := 3) (by norm_num)).2
  have hl3 : log (3 : ℝ) ≤ (10987 / 10000 : ℝ) := by
    apply hl.trans
    norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, sum_range_succ]
  have hf := buchstab_four_identity hω
  norm_num at hj
  linarith

/-- A directed rational cap for one scalar Buchstab panel above three.
Wu 2004 Lemma 2.10 page 9, derived interval certificate data. -/
def tailFiveCapQ (a b : ℚ) : ℚ := Wu04JCertificate.up
  ((1 + Wu04Integral.logUpperQ 12 (b - 1) + Burst9Psi2.jUpperSum (b - 1) 16) / a)

/-- The rational panel cap bounds omega throughout its panel.
Wu 2004 Lemma 2.10 page 9, derived certified delay quadrature. -/
theorem buchstab_le_tailFiveCap {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {a b : ℚ} (ha : 3 ≤ a) (hab : a ≤ b) (hb : b ≤ 4)
    {u : ℝ} (hu : u ∈ Set.Icc (a : ℝ) (b : ℝ)) : ω u ≤ (tailFiveCapQ a b : ℝ) := by
  have ha' : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hb' : (b : ℝ) ≤ 4 := by exact_mod_cast hb
  have hupos : 0 < u := by linarith [hu.1]
  have hformula := buchstab_three_four_formula hω (u := u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hj := Burst9Psi2.J_upper_of_cert (c := b - 1) (m := 16)
    (U := Burst9Psi2.jUpperSum (b - 1) 16) (by norm_num) (by linarith) le_rfl
  norm_num only [Rat.cast_sub, Rat.cast_one] at hj
  have hmono := J_mono_after_two (by linarith [hu.1] : 2 ≤ u - 1) (by linarith [hu.2] : u - 1 ≤ b - 1)
  have hl := (log_le_log (by linarith [hu.1] : 0 < u - 1) (by linarith [hu.2] : u - 1 ≤ b - 1)).trans
    (Wu04Integral.log_bounds 12 (y := (b : ℝ) - 1) (by linarith)).2
  have hnum : 1 + log (u - 1) + J 2 (u - 1) ≤
      (1 + Wu04Integral.logUpperQ 12 (b - 1) + Burst9Psi2.jUpperSum (b - 1) 16 : ℚ) := by
    push_cast
    rw [Wu04Integral.logUpperQ_cast]
    norm_num only [Rat.cast_sub, Rat.cast_one]
    linarith
  have hnum0 : 0 ≤ 1 + log (u - 1) + J 2 (u - 1) := by
    have hJ0 : 0 ≤ J 2 (u - 1) := by
      apply intervalIntegral.integral_nonneg (by linarith [hu.1])
      intro t ht
      exact div_nonneg (log_nonneg (by linarith [ht.1])) (by linarith [ht.1])
    linarith [log_nonneg (by linarith [hu.1] : 1 ≤ u - 1)]
  have hr : (((1 + Wu04Integral.logUpperQ 12 (b - 1) + Burst9Psi2.jUpperSum (b - 1) 16) / a : ℚ) : ℝ) ≤
      (tailFiveCapQ a b : ℝ) := by exact_mod_cast Wu04JCertificate.le_up _
  calc
    ω u = (1 + log (u - 1) + J 2 (u - 1)) / u := (eq_div_iff hupos.ne').mpr (by nlinarith)
    _ ≤ ((1 + Wu04Integral.logUpperQ 12 (b - 1) + Burst9Psi2.jUpperSum (b - 1) 16 : ℚ) : ℝ) / u :=
      div_le_div_of_nonneg_right hnum hupos.le
    _ ≤ ((1 + Wu04Integral.logUpperQ 12 (b - 1) + Burst9Psi2.jUpperSum (b - 1) 16 : ℚ) : ℝ) / a :=
      div_le_div_of_nonneg_left (hnum0.trans hnum) (by linarith) hu.1
    _ ≤ _ := by simpa only [Rat.cast_div] using hr

end LeanLab.ChenDoubleSieve.Task587
