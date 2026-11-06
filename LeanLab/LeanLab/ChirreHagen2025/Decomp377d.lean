import LeanLab.ChirreHagen2025.Statements

/-!
P0075 page 4, the gamma estimate after equation 2.4.
Chandee Lemma 2.3 and its Appendix, preprint pages 12 and 13.
https://arxiv.org/abs/0906.4177
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp377d
open MeasureTheory

/-- Chandee page 12, the real Binet remainder integrand. -/
noncomputable def binetKernel (z : ℂ) (u : ℝ) : ℝ :=
  -(2 * u * (u ^ 2 + z.re ^ 2 - z.im ^ 2)) /
    (((u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2) *
      (Real.exp (2 * Real.pi * u) - 1))

/-- Chandee page 12, the real remainder I at z. -/
noncomputable def binetRemainder (z : ℂ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), binetKernel z u

private lemma binetKernel_abs_le_two (a b : ℝ) (ha : 0 < a) {u : ℝ} (hu : 0 < u) :
    2 * |u ^ 2 + a ^ 2 - b ^ 2| / ((u ^ 2 + a ^ 2 - b ^ 2) ^ 2 + 4 * a ^ 2 * b ^ 2)
      ≤ 1 / (a * |b|) + 2 / a ^ 2 := by
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    have hu2 : 0 < u ^ 2 + a ^ 2 := by positivity
    have h1 : 1 / (a * |(0 : ℝ)|) = 0 := by simp
    rw [h1, zero_add]
    have h2 : 2 * |u ^ 2 + a ^ 2 - 0 ^ 2| / ((u ^ 2 + a ^ 2 - 0 ^ 2) ^ 2 + 4 * a ^ 2 * 0 ^ 2)
        = 2 / (u ^ 2 + a ^ 2) := by
      simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, add_zero, sub_zero]
      rw [abs_of_pos hu2]
      field_simp
    rw [h2]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : a ^ 2 ≤ u ^ 2 + a ^ 2 := by nlinarith
    exact this
  · have hbpos : 0 < |b| := abs_pos.mpr hb
    have hM : 0 < (u ^ 2 + a ^ 2 - b ^ 2) ^ 2 + 4 * a ^ 2 * b ^ 2 := by
      have : 0 < 4 * a ^ 2 * b ^ 2 := by positivity
      nlinarith
    have hamgm : 4 * a * |b| * |u ^ 2 + a ^ 2 - b ^ 2|
        ≤ (u ^ 2 + a ^ 2 - b ^ 2) ^ 2 + 4 * a ^ 2 * b ^ 2 := by
      nlinarith [sq_nonneg (|u ^ 2 + a ^ 2 - b ^ 2| - 2 * a * |b|),
        sq_abs (u ^ 2 + a ^ 2 - b ^ 2), sq_abs b]
    rcases eq_or_ne (u ^ 2 + a ^ 2 - b ^ 2) 0 with hD | hD
    · rw [hD]
      simp only [abs_zero, mul_zero, zero_div]
      positivity
    · have hDpos : 0 < |u ^ 2 + a ^ 2 - b ^ 2| := abs_pos.mpr hD
      have step : 2 * |u ^ 2 + a ^ 2 - b ^ 2| /
            ((u ^ 2 + a ^ 2 - b ^ 2) ^ 2 + 4 * a ^ 2 * b ^ 2)
          ≤ 2 * |u ^ 2 + a ^ 2 - b ^ 2| / (4 * a * |b| * |u ^ 2 + a ^ 2 - b ^ 2|) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hamgm
      have hval : 2 * |u ^ 2 + a ^ 2 - b ^ 2| / (4 * a * |b| * |u ^ 2 + a ^ 2 - b ^ 2|)
          = 1 / (2 * a * |b|) := by
        field_simp
        norm_num
      rw [hval] at step
      refine step.trans ?_
      have h1 : 0 < a * |b| := by positivity
      have h2 : 0 < a := ha
      have h3 : 1 / (2 * a * |b|) ≤ 1 / (a * |b|) := by
        apply div_le_div_of_nonneg_left (by norm_num)
        · positivity
        · nlinarith
      have h4 : 0 ≤ 2 / a ^ 2 := by positivity
      linarith

private lemma binetKernel_bound (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) {u : ℝ} (hu : 0 < u) :
    ‖binetKernel z u‖ ≤
      (1 / (z.re * |z.im|) + 2 / z.re ^ 2) *
        (u / (Real.exp (2 * Real.pi * u) - 1)) := by
  have ha : 0 < z.re := by linarith
  have hE : 0 < Real.exp (2 * Real.pi * u) - 1 := by
    have h : Real.exp 0 < Real.exp (2 * Real.pi * u) :=
      Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    simpa using h
  have hM : 0 < (u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
    rcases eq_or_ne z.im 0 with hb | hb
    · simp only [hb]
      have h2 : 0 < u ^ 2 + z.re ^ 2 := by positivity
      nlinarith
    · have h2 : 0 < 4 * z.re ^ 2 * z.im ^ 2 := by positivity
      nlinarith
  have hstep := binetKernel_abs_le_two z.re z.im ha hu
  have hDpos : 0 ≤ |u ^ 2 + z.re ^ 2 - z.im ^ 2| := abs_nonneg _
  have hexp : (0:ℝ) < Real.exp (2 * Real.pi * u) := Real.exp_pos _
  have hnorm : ‖binetKernel z u‖ = 2 * u * |u ^ 2 + z.re ^ 2 - z.im ^ 2| /
      (((u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2) *
        (Real.exp (2 * Real.pi * u) - 1)) := by
    simp only [binetKernel, Real.norm_eq_abs, abs_div, abs_neg, abs_mul, abs_two,
      abs_of_pos hu, abs_of_pos (mul_pos hM hE)]
  rw [hnorm]
  rw [show 2 * u * |u ^ 2 + z.re ^ 2 - z.im ^ 2| /
        (((u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2) *
          (Real.exp (2 * Real.pi * u) - 1))
      = (u / (Real.exp (2 * Real.pi * u) - 1)) *
        (2 * |u ^ 2 + z.re ^ 2 - z.im ^ 2| /
          ((u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2)) from by
    field_simp]
  rw [mul_comm ((1 / (z.re * |z.im|) + 2 / z.re ^ 2))]
  exact mul_le_mul_of_nonneg_left hstep (le_of_lt (div_pos hu hE))

private lemma exp_two_pi_mul_sub_one_pos {u : ℝ} (hu : 0 < u) :
    0 < Real.exp (2 * Real.pi * u) - 1 := by
  have h : Real.exp 0 < Real.exp (2 * Real.pi * u) :=
    Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  simpa using h

private lemma continuousOn_div_exp_two_pi :
    ContinuousOn (fun u : ℝ => u / (Real.exp (2 * Real.pi * u) - 1)) (Set.Ioi 0) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro u hu
    exact ne_of_gt (exp_two_pi_mul_sub_one_pos hu)

private lemma integrableOn_div_exp_two_pi_Ioc :
    IntegrableOn (fun u : ℝ => u / (Real.exp (2 * Real.pi * u) - 1)) (Set.Ioc 0 1) := by
  refine IntegrableOn.of_bound (μ := volume) (s := Set.Ioc 0 1) measure_Ioc_lt_top
    ((continuousOn_div_exp_two_pi.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc) (1 / (2 * Real.pi)) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall (fun u hu => ?_)
  have hu0 : 0 < u := hu.1
  have hE := exp_two_pi_mul_sub_one_pos hu0
  have hb : 2 * Real.pi * u ≤ Real.exp (2 * Real.pi * u) - 1 := by
    have h := Real.add_one_le_exp (2 * Real.pi * u)
    linarith
  have hpos : 0 < 2 * Real.pi * u := by positivity
  rw [Real.norm_eq_abs, abs_of_pos (div_pos hu0 hE)]
  have step : u / (Real.exp (2 * Real.pi * u) - 1) ≤ u / (2 * Real.pi * u) :=
    div_le_div_of_nonneg_left (le_of_lt hu0) hpos hb
  have hval : u / (2 * Real.pi * u) = 1 / (2 * Real.pi) := by
    field_simp
  linarith [step, hval.symm ▸ step]

private lemma integrableOn_two_mul_exp_tail :
    IntegrableOn (fun u : ℝ => 2 * (u * Real.exp (-(2 * Real.pi) * u))) (Set.Ioi 1) := by
  have hbase : IntegrableOn (fun u : ℝ => u ^ (1 : ℝ) * Real.exp (-(2 * Real.pi) * u ^ (1 : ℝ)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 2 * Real.pi)
      (by norm_num) (by norm_num) (by positivity)
  have h0 : IntegrableOn (fun u : ℝ => u * Real.exp (-(2 * Real.pi) * u)) (Set.Ioi 0) := by
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro x _
    simp [Real.rpow_one]
  have hsub : IntegrableOn (fun u : ℝ => u * Real.exp (-(2 * Real.pi) * u)) (Set.Ioi 1) :=
    h0.mono_set (Set.Ioi_subset_Ioi (by norm_num))
  exact Integrable.const_mul hsub 2

private lemma integrableOn_div_exp_two_pi :
    IntegrableOn (fun u : ℝ => u / (Real.exp (2 * Real.pi * u) - 1)) (Set.Ioi 0) := by
  have htail : IntegrableOn (fun u : ℝ => u / (Real.exp (2 * Real.pi * u) - 1)) (Set.Ioi 1) := by
    refine Integrable.mono' integrableOn_two_mul_exp_tail
      ((continuousOn_div_exp_two_pi.mono (Set.Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable
        measurableSet_Ioi) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu1 : 1 < u := hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu1
    have hE := exp_two_pi_mul_sub_one_pos hu0
    have hexp : (2 : ℝ) ≤ Real.exp (2 * Real.pi * u) := by
      have h1 : Real.exp 1 ≤ Real.exp (2 * Real.pi * u) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_gt_three]
      linarith [Real.exp_one_gt_two]
    have hhalf : Real.exp (2 * Real.pi * u) / 2 ≤ Real.exp (2 * Real.pi * u) - 1 := by linarith
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hu0 hE)]
    have step : u / (Real.exp (2 * Real.pi * u) - 1) ≤
        u / (Real.exp (2 * Real.pi * u) / 2) :=
      div_le_div_of_nonneg_left (le_of_lt hu0) (by positivity) hhalf
    have hval : u / (Real.exp (2 * Real.pi * u) / 2) =
        2 * (u * Real.exp (-(2 * Real.pi) * u)) := by
      rw [show -(2 * Real.pi) * u = -(2 * Real.pi * u) by ring, Real.exp_neg]
      field_simp
    linarith [hval ▸ step]
  have hsplit : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hsplit]
  exact integrableOn_div_exp_two_pi_Ioc.union htail

private lemma integrableOn_binetKernel (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    IntegrableOn (binetKernel z) (Set.Ioi 0) := by
  have ha : 0 < z.re := by linarith
  have hC : 0 ≤ 1 / (z.re * |z.im|) + 2 / z.re ^ 2 := by positivity
  refine Integrable.mono' (g := fun u : ℝ =>
    (1 / (z.re * |z.im|) + 2 / z.re ^ 2) * (u / (Real.exp (2 * Real.pi * u) - 1)))
    (Integrable.const_mul integrableOn_div_exp_two_pi _) ?_ ?_
  · have hc : ContinuousOn (binetKernel z) (Set.Ioi 0) := by
      unfold binetKernel
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro u hu
        have hE := exp_two_pi_mul_sub_one_pos hu
        have hM : 0 < (u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
          rcases eq_or_ne z.im 0 with hb | hb
          · simp only [hb]
            have h2 : 0 < u ^ 2 + z.re ^ 2 := by positivity
            nlinarith
          · have h2 : 0 < 4 * z.re ^ 2 * z.im ^ 2 := by positivity
            nlinarith
        exact ne_of_gt (mul_pos hM hE)
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    exact binetKernel_bound z hz hu

private lemma binetNormSq_denominator (z : ℂ) (u : ℝ) :
    Complex.normSq ((u : ℂ) ^ 2 + z ^ 2) =
      (u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
  simp [Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im]
  ring

private lemma binet_denominator_ne (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    {u : ℝ} (hu : 0 < u) : (u : ℂ) ^ 2 + z ^ 2 ≠ 0 := by
  intro hw
  have hM : 0 < (u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
    rcases eq_or_ne z.im 0 with hb | hb
    · simp only [hb]
      have h2 : 0 < u ^ 2 + z.re ^ 2 := by positivity
      nlinarith
    · have h2 : 0 < 4 * z.re ^ 2 * z.im ^ 2 := by positivity
      nlinarith
  have heq := congrArg Complex.normSq hw
  rw [binetNormSq_denominator] at heq
  simp at heq
  linarith

private lemma binetRatio_re (z : ℂ) (u : ℝ) :
    ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re =
      u * (u ^ 2 + z.re ^ 2 - z.im ^ 2) /
        ((u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2) := by
  rw [Complex.div_re, binetNormSq_denominator]
  simp [pow_two, Complex.mul_re, Complex.mul_im]
  ring

private lemma binetRatioDerivative_abs_le (z : ℂ) (u : ℝ) :
    |(((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re)| ≤
      (‖z‖ ^ 2 + u ^ 2) / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
  calc
    |(((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re)| ≤
        ‖(z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2‖ :=
      Complex.abs_re_le_norm _
    _ = ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
      rw [norm_div, norm_pow]
    _ ≤ (‖z‖ ^ 2 + u ^ 2) / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      calc
        ‖z ^ 2 - (u : ℂ) ^ 2‖ ≤ ‖z ^ 2‖ + ‖(u : ℂ) ^ 2‖ := norm_sub_le _ _
        _ = ‖z‖ ^ 2 + u ^ 2 := by
          simp [norm_pow, Complex.norm_real, abs_of_nonneg (sq_nonneg u)]

private lemma binet_norm_ge_two_mul_re_im (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (u : ℝ) :
    2 * z.re * |z.im| ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ := by
  have hs : (2 * z.re * |z.im|) ^ 2 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, binetNormSq_denominator]
    nlinarith [sq_nonneg (u ^ 2 + z.re ^ 2 - z.im ^ 2), sq_abs z.im]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hs

private lemma binet_norm_ge_quarter (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hzy : z.re ^ 2 < z.im ^ 2) (hn : 4 ≤ ‖z‖) (u : ℝ) :
    ‖z‖ / 4 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ := by
  have hM : 4 * z.re ^ 2 * z.im ^ 2 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, binetNormSq_denominator]
    nlinarith [sq_nonneg (u ^ 2 + z.re ^ 2 - z.im ^ 2)]
  by_cases hcase : ‖z‖ ^ 4 ≤ 4 * z.re ^ 2 * z.im ^ 2
  · have hs : ‖z‖ ^ 2 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ := by
      apply (sq_le_sq₀ (sq_nonneg ‖z‖) (norm_nonneg _)).mp
      calc
        (‖z‖ ^ 2) ^ 2 = ‖z‖ ^ 4 := by ring
        _ ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := hcase.trans hM
    have hr : ‖z‖ / 4 ≤ ‖z‖ ^ 2 := by nlinarith
    exact hr.trans hs
  · have habs : |z.re| ≤ |z.im| := sq_le_sq.mp hzy.le
    have hre : 0 ≤ z.re := by linarith
    have hn2 : ‖z‖ ≤ 2 * |z.im| := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 2 * |z.im| := by linarith
    have hmul := mul_le_mul_of_nonneg_right (show 2 ≤ 8 * z.re by linarith) (abs_nonneg z.im)
    have hq : ‖z‖ / 4 ≤ 2 * z.re * |z.im| := by nlinarith
    exact hq.trans (binet_norm_ge_two_mul_re_im z hz u)

private lemma binetRatioDerivative_low_bound (z : ℂ) (hn : 4 ≤ ‖z‖)
    {u : ℝ} (hu : 0 < u) (huR : u ≤ ‖z‖ / 3) :
    |(((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re)| ≤
      45 / (32 * ‖z‖ ^ 2) := by
  have hr : 0 < ‖z‖ := by linarith
  have hrev : ‖z‖ ^ 2 - u ^ 2 ≤ ‖z ^ 2 + (u : ℂ) ^ 2‖ := by
    have h := norm_sub_norm_le (z ^ 2) (-(u : ℂ) ^ 2)
    simpa [norm_pow, Complex.norm_real, sub_neg_eq_add, abs_of_nonneg (sq_nonneg u)] using h
  have hw : ‖z ^ 2 + (u : ℂ) ^ 2‖ = ‖(u : ℂ) ^ 2 + z ^ 2‖ := by rw [add_comm]
  rw [hw] at hrev
  have hu2 : u ^ 2 ≤ ‖z‖ ^ 2 / 9 := by nlinarith
  have hlow : 8 * ‖z‖ ^ 2 / 9 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ := by nlinarith
  have hden : (8 * ‖z‖ ^ 2 / 9) ^ 2 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hlow
  refine (binetRatioDerivative_abs_le z u).trans ?_
  calc
    (‖z‖ ^ 2 + u ^ 2) / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 ≤
        (10 * ‖z‖ ^ 2 / 9) / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 :=
      div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg _)
    _ ≤ (10 * ‖z‖ ^ 2 / 9) / (8 * ‖z‖ ^ 2 / 9) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 45 / (32 * ‖z‖ ^ 2) := by field_simp; ring

private lemma binetRatioDerivative_tail_bound (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hzy : z.re ^ 2 < z.im ^ 2) (hn : 4 ≤ ‖z‖) (u : ℝ) :
    |(((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re)| ≤
      3 / ‖z‖ + 18 := by
  have hr : 0 < ‖z‖ := by linarith
  have hre : 0 ≤ z.re := by linarith
  have habs : |z.re| ≤ |z.im| := sq_le_sq.mp hzy.le
  have hr2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hb : ‖z‖ ≤ 3 / 2 * |z.im| := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [abs_of_nonneg hre] at habs
    nlinarith [sq_abs z.im, sq_abs z.re]
  have hb' : 2 * ‖z‖ / 3 ≤ |z.im| := by linarith
  have hm := mul_le_mul_of_nonneg_left hb' (show 0 ≤ 2 * z.re by positivity)
  have hm2 := mul_le_mul_of_nonneg_right (show 1 ≤ 4 * z.re by linarith)
    (show 0 ≤ ‖z‖ / 3 by positivity)
  have hab : ‖z‖ / 3 ≤ 2 * z.re * |z.im| := by nlinarith
  have hw : ‖z‖ / 3 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ :=
    hab.trans (binet_norm_ge_two_mul_re_im z hz u)
  have hu2 : u ^ 2 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ + ‖z‖ ^ 2 := by
    have h := norm_sub_le ((u : ℂ) ^ 2 + z ^ 2) (z ^ 2)
    simpa [norm_pow, Complex.norm_real, abs_of_nonneg (sq_nonneg u)] using h
  have hnorm : 0 < ‖(u : ℂ) ^ 2 + z ^ 2‖ := by linarith
  refine (binetRatioDerivative_abs_le z u).trans ?_
  calc
    (‖z‖ ^ 2 + u ^ 2) / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 ≤
        (2 * ‖z‖ ^ 2 + ‖(u : ℂ) ^ 2 + z ^ 2‖) / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 :=
      div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg _)
    _ = 1 / ‖(u : ℂ) ^ 2 + z ^ 2‖ + 2 * ‖z‖ ^ 2 / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
      field_simp
      ring
    _ ≤ 3 / ‖z‖ + 18 := by
      have h1 : 1 / ‖(u : ℂ) ^ 2 + z ^ 2‖ ≤ 3 / ‖z‖ := by
        rw [div_le_div_iff₀ hnorm hr]
        nlinarith
      have h2 : 2 * ‖z‖ ^ 2 / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 ≤ 18 := by
        rw [div_le_iff₀ (by positivity)]
        have hw2 := (sq_le_sq₀ (by positivity : 0 ≤ ‖z‖ / 3) (norm_nonneg _)).mpr hw
        nlinarith [sq_nonneg ‖z‖]
      linarith

private lemma continuousOn_binetRatio_re (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    ContinuousOn (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re) (Set.Ioi 0) := by
  fun_prop (disch := intro u hu; exact binet_denominator_ne z hz hu)

private lemma continuousOn_binetRatioDerivative_re (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    ContinuousOn (fun u : ℝ => ((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re)
      (Set.Ioi 0) := by
  fun_prop (disch := intro u hu; exact pow_ne_zero 2 (binet_denominator_ne z hz hu))

private lemma hasDerivAt_binetRatio_re (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t : ℝ => ((t : ℂ) / ((t : ℂ) ^ 2 + z ^ 2)).re)
      (((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re) u := by
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u :=
    HasDerivAt.ofReal_comp (hasDerivAt_id u)
  have hsq : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2) (2 * (u : ℂ)) u := by
    convert hc.pow 2 using 1 <;> simp
  have hquot := hc.div (hsq.add_const (z ^ 2)) (binet_denominator_ne z hz hu)
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hquot
  convert hre using 1
  · ext t
    rfl
  · congr 1
    ring

private lemma one_sub_exp_two_pi_pos {u : ℝ} (hu : 0 < u) :
    0 < 1 - Real.exp (-(2 * Real.pi * u)) := by
  have h : Real.exp (-(2 * Real.pi * u)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  linarith

private lemma binetLog_nonpos {u : ℝ} (hu : 0 < u) :
    Real.log (1 - Real.exp (-(2 * Real.pi * u))) ≤ 0 := by
  apply Real.log_nonpos (one_sub_exp_two_pi_pos hu).le
  have h : Real.exp (-(2 * Real.pi * u)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hp := Real.exp_pos (-(2 * Real.pi * u))
  linarith

private lemma hasDerivAt_binetLog {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t : ℝ => Real.log (1 - Real.exp (-(2 * Real.pi * t))))
      (2 * Real.pi / (Real.exp (2 * Real.pi * u) - 1)) u := by
  have hlin : HasDerivAt (fun t : ℝ => -(2 * Real.pi * t)) (-(2 * Real.pi)) u := by
    simpa using (hasDerivAt_id u).const_mul (-(2 * Real.pi))
  have hsub := HasDerivAt.const_sub 1 hlin.exp
  have hlog := hsub.log (one_sub_exp_two_pi_pos hu).ne'
  convert hlog using 1
  rw [Real.exp_neg]
  field_simp [ne_of_gt (exp_two_pi_mul_sub_one_pos hu), ne_of_gt (Real.exp_pos (2 * Real.pi * u))]

private lemma hasSum_binetLog_terms {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1))
      (-Real.log (1 - Real.exp (-(2 * Real.pi * u)))) := by
  have hx : |Real.exp (-(2 * Real.pi * u))| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  convert Real.hasSum_pow_div_log_of_abs_lt_one hx using 1 with n
  funext n
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

private lemma integrableOn_binetLog_term (n : ℕ) :
    IntegrableOn (fun u : ℝ => Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1))
      (Set.Ioi 0) := by
  have hp : 0 < 2 * Real.pi * (n + 1) := by positivity
  have ha : -(2 * Real.pi * (n + 1)) < 0 := by linarith
  exact (integrableOn_exp_mul_Ioi ha 0).div_const (n + 1)

private lemma integral_binetLog_term (n : ℕ) :
    (∫ u : ℝ in Set.Ioi 0, Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)) =
      1 / (2 * Real.pi * (n + 1) ^ 2) := by
  have hp : 0 < 2 * Real.pi * (n + 1) := by positivity
  have ha : -(2 * Real.pi * (n + 1)) < 0 := by linarith
  rw [MeasureTheory.integral_div, integral_exp_mul_Ioi ha]
  simp only [mul_zero, Real.exp_zero, Nat.cast_add, Nat.cast_one]
  field_simp [Real.pi_ne_zero]

private lemma hasSum_binetLog_term_integrals :
    HasSum (fun n : ℕ => ∫ u : ℝ in Set.Ioi 0,
      Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)) (Real.pi / 12) := by
  have hshift : HasSum (fun n : ℕ => (1 : ℝ) / (n + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h0 : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
        (Real.pi ^ 2 / 6 + ∑ i ∈ Finset.range 1, (1 : ℝ) / (i : ℝ) ^ 2) := by
      simpa using hasSum_zeta_two
    have h := (hasSum_nat_add_iff 1).mpr h0
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hmul := hshift.mul_left (1 / (2 * Real.pi))
  convert hmul using 1
  · funext n
    rw [integral_binetLog_term]
    push_cast
    field_simp [Real.pi_ne_zero, show (n : ℝ) + 1 ≠ 0 by positivity]
  · field_simp [Real.pi_ne_zero]
    ring

private lemma integral_negLog_one_sub_exp :
    (∫ u : ℝ in Set.Ioi 0, -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) =
      Real.pi / 12 := by
  have hsum_norm : Summable (fun n : ℕ => ∫ u : ℝ in Set.Ioi 0,
      ‖Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)‖) := by
    have hnorm : ∀ n : ℕ, (∫ u : ℝ in Set.Ioi 0,
        ‖Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)‖) =
        (∫ u : ℝ in Set.Ioi 0, Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)) := by
      intro n
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le (by positivity))
    simpa only [hnorm] using hasSum_binetLog_term_integrals.summable
  have hsum := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun (n : ℕ) (u : ℝ) => Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1))
    integrableOn_binetLog_term hsum_norm
  have heval : (∫ u : ℝ in Set.Ioi 0, ∑' n : ℕ,
      Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)) = Real.pi / 12 :=
    hsum.unique hasSum_binetLog_term_integrals
  rw [← heval]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (hasSum_binetLog_terms hu).tsum_eq.symm

private lemma integral_binetLog_term_tail (n : ℕ) (R : ℝ) :
    (∫ u : ℝ in Set.Ioi R, Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)) =
      Real.exp (-(2 * Real.pi * (n + 1) * R)) / (2 * Real.pi * (n + 1) ^ 2) := by
  have hp : 0 < 2 * Real.pi * (n + 1) := by positivity
  have ha : -(2 * Real.pi * (n + 1)) < 0 := by linarith
  rw [MeasureTheory.integral_div, integral_exp_mul_Ioi ha]
  field_simp [Real.pi_ne_zero]

private lemma integrableOn_negLog_one_sub_exp :
    IntegrableOn (fun u : ℝ => -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) (Set.Ioi 0) := by
  by_contra h
  have hz : (∫ u : ℝ in Set.Ioi 0, -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) = 0 :=
    integral_undef h
  have he := integral_negLog_one_sub_exp
  rw [hz] at he
  have hp : 0 < Real.pi / 12 := by positivity
  linarith

private lemma integral_negLog_one_sub_exp_tail_pi_le {R : ℝ} (hR : 0 ≤ R) :
    (∫ u : ℝ in Set.Ioi R, -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) ≤
      (Real.pi / 12) * Real.exp (-(2 * Real.pi * R)) := by
  have hbase : Summable (fun n : ℕ => 1 / (2 * Real.pi * (n + 1) ^ 2)) := by
    simpa only [integral_binetLog_term] using hasSum_binetLog_term_integrals.summable
  have hnorm : ∀ n : ℕ, (∫ u : ℝ in Set.Ioi R,
      ‖Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)‖) =
      Real.exp (-(2 * Real.pi * (n + 1) * R)) / (2 * Real.pi * (n + 1) ^ 2) := by
    intro n
    rw [← integral_binetLog_term_tail n R]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le (by positivity))
  have hsummable : Summable (fun n : ℕ => ∫ u : ℝ in Set.Ioi R,
      ‖Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)‖) := by
    apply hbase.of_nonneg_of_le
    · intro n
      rw [hnorm]
      positivity
    · intro n
      rw [hnorm]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Real.exp_le_one_iff.mpr
      have hp : 0 ≤ 2 * Real.pi * (n + 1) * R := by positivity
      linarith
  have hsum := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioi R))
    (F := fun (n : ℕ) (u : ℝ) => Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1))
    (fun n => (integrableOn_exp_mul_Ioi (show -(2 * Real.pi * (n + 1)) < 0 by
      nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) n]) R).div_const
      (n + 1)) hsummable
  have heval : (∫ u : ℝ in Set.Ioi R, -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) =
      ∑' n : ℕ, (∫ u : ℝ in Set.Ioi R, Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)) := by
    rw [hsum.tsum_eq]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hasSum_binetLog_terms (lt_of_le_of_lt hR hu)).tsum_eq.symm
  have hterm_summable : Summable (fun n : ℕ => ∫ u : ℝ in Set.Ioi R,
      Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)) := by
    apply hbase.of_nonneg_of_le
    · intro n
      rw [integral_binetLog_term_tail]
      positivity
    · intro n
      rw [integral_binetLog_term_tail]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Real.exp_le_one_iff.mpr
      have hp : 0 ≤ 2 * Real.pi * (n + 1) * R := by positivity
      linarith
  have hle : (∑' n : ℕ, (∫ u : ℝ in Set.Ioi R,
      Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1))) ≤
      ∑' n : ℕ, Real.exp (-(2 * Real.pi * R)) *
        (∫ u : ℝ in Set.Ioi 0, Real.exp (-(2 * Real.pi * (n + 1)) * u) / (n + 1)) := by
    refine Summable.tsum_le_tsum (fun n => ?_) hterm_summable
      (hasSum_binetLog_term_integrals.mul_left (Real.exp (-(2 * Real.pi * R)))).summable
    rw [integral_binetLog_term_tail, integral_binetLog_term]
    have he : Real.exp (-(2 * Real.pi * (n + 1) * R)) ≤ Real.exp (-(2 * Real.pi * R)) := by
      apply Real.exp_le_exp.mpr
      have hn1 : 1 ≤ (n : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hm := mul_le_mul_of_nonneg_left hn1 hR
      have hm2 := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * Real.pi by positivity)
      nlinarith
    calc
      Real.exp (-(2 * Real.pi * (n + 1) * R)) / (2 * Real.pi * (n + 1) ^ 2) ≤
          Real.exp (-(2 * Real.pi * R)) / (2 * Real.pi * (n + 1) ^ 2) :=
        div_le_div_of_nonneg_right he (by positivity)
      _ = Real.exp (-(2 * Real.pi * R)) * (1 / (2 * Real.pi * (n + 1) ^ 2)) := by ring
  rw [heval]
  calc
    _ ≤ _ := hle
    _ = Real.exp (-(2 * Real.pi * R)) * (Real.pi / 12) :=
      (hasSum_binetLog_term_integrals.mul_left (Real.exp (-(2 * Real.pi * R)))).tsum_eq
    _ = (Real.pi / 12) * Real.exp (-(2 * Real.pi * R)) := by ring

private lemma negLog_one_sub_le_two_mul {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hden : 0 < 1 - x := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 / (1 - x) by positivity)
  rw [Real.log_div one_ne_zero hden.ne', Real.log_one, zero_sub] at h
  refine h.trans ?_
  calc
    1 / (1 - x) - 1 = x / (1 - x) := by field_simp; ring
    _ ≤ 2 * x := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [sq_nonneg x]

private lemma negLog_one_sub_exp_le_two_mul_exp {u : ℝ} (hu : 1 ≤ u) :
    -Real.log (1 - Real.exp (-(2 * Real.pi * u))) ≤ 2 * Real.exp (-(2 * Real.pi * u)) := by
  have hE : 2 ≤ Real.exp (2 * Real.pi * u) := by
    calc
      2 ≤ Real.exp 1 := Real.exp_one_gt_two.le
      _ ≤ Real.exp (2 * Real.pi * u) := Real.exp_le_exp.mpr (by
        have hmul := mul_le_mul_of_nonneg_left hu (show 0 ≤ 2 * Real.pi by positivity)
        nlinarith [Real.pi_gt_three])
  have hx0 : 0 < Real.exp (-(2 * Real.pi * u)) := Real.exp_pos _
  have hx2 : Real.exp (-(2 * Real.pi * u)) ≤ 1 / 2 := by
    rw [show -(2 * Real.pi * u) = -(2 * Real.pi * u) by ring, Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hE
  exact negLog_one_sub_le_two_mul hx0 hx2

private lemma integral_negLog_one_sub_exp_tail_le {R : ℝ} (hR : 1 ≤ R) :
    (∫ u : ℝ in Set.Ioi R, -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) ≤
      Real.exp (-(2 * Real.pi * R)) / Real.pi := by
  have hlog : IntegrableOn (fun u : ℝ => -Real.log (1 - Real.exp (-(2 * Real.pi * u))))
      (Set.Ioi R) := integrableOn_negLog_one_sub_exp.mono_set (Set.Ioi_subset_Ioi (by linarith))
  have hexp : IntegrableOn (fun u : ℝ => 2 * Real.exp (-(2 * Real.pi * u))) (Set.Ioi R) := by
    have ha : -(2 * Real.pi) < 0 := by nlinarith [Real.pi_pos]
    simpa only [IntegrableOn, neg_mul] using (integrableOn_exp_mul_Ioi ha R).const_mul 2
  have hle := integral_mono_ae hlog hexp (show
    (fun u : ℝ => -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) ≤ᵐ[volume.restrict (Set.Ioi R)]
      (fun u => 2 * Real.exp (-(2 * Real.pi * u))) by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u := hR.trans hu.le
    exact negLog_one_sub_exp_le_two_mul_exp hu1)
  have hval : (∫ u : ℝ in Set.Ioi R, 2 * Real.exp (-(2 * Real.pi * u))) =
      Real.exp (-(2 * Real.pi * R)) / Real.pi := by
    rw [integral_const_mul]
    have ha : -(2 * Real.pi) < 0 := by nlinarith [Real.pi_pos]
    have he := integral_exp_mul_Ioi ha R
    simp only [neg_mul] at he
    rw [he]
    field_simp [Real.pi_ne_zero]
  rw [hval] at hle
  exact hle

private lemma continuousOn_mul_negLog_one_sub_exp :
    ContinuousOn (fun u : ℝ => u * (-Real.log (1 - Real.exp (-(2 * Real.pi * u)))))
      (Set.Ioi 0) := by
  apply ContinuousOn.mul continuousOn_id
  apply ContinuousOn.neg
  apply ContinuousOn.log
  · fun_prop
  · intro u hu
    exact (one_sub_exp_two_pi_pos hu).ne'

private lemma integrableOn_mul_negLog_one_sub_exp :
    IntegrableOn (fun u : ℝ => u * (-Real.log (1 - Real.exp (-(2 * Real.pi * u)))))
      (Set.Ioi 0) := by
  have hlow : IntegrableOn (fun u : ℝ => u * (-Real.log (1 - Real.exp (-(2 * Real.pi * u)))))
      (Set.Ioc 0 1) := by
    refine Integrable.mono' (g := fun u : ℝ => -Real.log (1 - Real.exp (-(2 * Real.pi * u))))
      (integrableOn_negLog_one_sub_exp.mono_set Set.Ioc_subset_Ioi_self)
      ((continuousOn_mul_negLog_one_sub_exp.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable
        measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hL : 0 ≤ -Real.log (1 - Real.exp (-(2 * Real.pi * u))) := neg_nonneg.mpr (binetLog_nonpos hu.1)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu.1.le hL)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) hL]
  have hhigh : IntegrableOn (fun u : ℝ => u * (-Real.log (1 - Real.exp (-(2 * Real.pi * u)))))
      (Set.Ioi 1) := by
    refine Integrable.mono' (g := fun u : ℝ => 2 * (u * Real.exp (-(2 * Real.pi) * u)))
      integrableOn_two_mul_exp_tail
      ((continuousOn_mul_negLog_one_sub_exp.mono (Set.Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable
        measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u := hu.le
    have hL : 0 ≤ -Real.log (1 - Real.exp (-(2 * Real.pi * u))) := neg_nonneg.mpr (binetLog_nonpos (by linarith))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) hL)]
    have h := mul_le_mul_of_nonneg_left (negLog_one_sub_exp_le_two_mul_exp hu1) (show 0 ≤ u by linarith)
    simpa only [neg_mul, mul_neg, mul_assoc, mul_comm, mul_left_comm] using h
  have hsplit : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hsplit]
  exact hlow.union hhigh

private lemma binetRatio_mul_logDeriv (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    {u : ℝ} (hu : 0 < u) :
    ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re * (2 * Real.pi / (Real.exp (2 * Real.pi * u) - 1)) =
      -Real.pi * binetKernel z u := by
  rw [binetRatio_re]
  unfold binetKernel
  field_simp [ne_of_gt (exp_two_pi_mul_sub_one_pos hu)]

private lemma integrableOn_binetRatio_mul_logDeriv (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    IntegrableOn (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
      (2 * Real.pi / (Real.exp (2 * Real.pi * u) - 1))) (Set.Ioi 0) := by
  have hi : IntegrableOn (fun u : ℝ => -Real.pi * binetKernel z u) (Set.Ioi 0) :=
    (integrableOn_binetKernel z hz).const_mul (-Real.pi)
  refine hi.congr_fun ?_ measurableSet_Ioi
  intro u hu
  exact (binetRatio_mul_logDeriv z hz hu).symm

private lemma binetRatio_abs_le (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hzy : z.re ^ 2 < z.im ^ 2) (hn : 4 ≤ ‖z‖) {u : ℝ} (hu : 0 < u) :
    |((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re| ≤ 4 * u / ‖z‖ := by
  have hr : 0 < ‖z‖ := by linarith
  have hw := binet_norm_ge_quarter z hz hzy hn u
  have hnorm : 0 < ‖(u : ℂ) ^ 2 + z ^ 2‖ := by linarith
  calc
    |((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re| ≤ ‖(u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)‖ :=
      Complex.abs_re_le_norm _
    _ = u / ‖(u : ℂ) ^ 2 + z ^ 2‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hu.le]
    _ ≤ 4 * u / ‖z‖ := by
      rw [div_le_div_iff₀ hnorm hr]
      nlinarith

private lemma integrableOn_binetRatio_mul_log (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hzy : z.re ^ 2 < z.im ^ 2) (hn : 4 ≤ ‖z‖) :
    IntegrableOn (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
      Real.log (1 - Real.exp (-(2 * Real.pi * u)))) (Set.Ioi 0) := by
  have hr : 0 < ‖z‖ := by linarith
  have hcont : ContinuousOn (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
      Real.log (1 - Real.exp (-(2 * Real.pi * u)))) (Set.Ioi 0) := by
    apply ContinuousOn.mul (continuousOn_binetRatio_re z hz)
    apply ContinuousOn.log
    · fun_prop
    · intro u hu
      exact (one_sub_exp_two_pi_pos hu).ne'
  refine Integrable.mono' (g := fun u : ℝ => (4 / ‖z‖) *
    (u * (-Real.log (1 - Real.exp (-(2 * Real.pi * u))))))
    (integrableOn_mul_negLog_one_sub_exp.const_mul (4 / ‖z‖))
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hL : 0 ≤ -Real.log (1 - Real.exp (-(2 * Real.pi * u))) := neg_nonneg.mpr (binetLog_nonpos hu)
  have hF := binetRatio_abs_le z hz hzy hn hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (binetLog_nonpos hu)]
  have hmul := mul_le_mul_of_nonneg_right hF hL
  calc
    |((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re| * -Real.log (1 - Real.exp (-(2 * Real.pi * u))) ≤
        (4 * u / ‖z‖) * -Real.log (1 - Real.exp (-(2 * Real.pi * u))) := hmul
    _ = (4 / ‖z‖) * (u * -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) := by ring

private lemma integrableOn_binetRatioDerivative_mul_log (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hzy : z.re ^ 2 < z.im ^ 2) (hn : 4 ≤ ‖z‖) :
    IntegrableOn (fun u : ℝ => ((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re *
      Real.log (1 - Real.exp (-(2 * Real.pi * u)))) (Set.Ioi 0) := by
  have hr : 0 < ‖z‖ := by linarith
  have hcont : ContinuousOn (fun u : ℝ => ((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re *
      Real.log (1 - Real.exp (-(2 * Real.pi * u)))) (Set.Ioi 0) := by
    apply ContinuousOn.mul (continuousOn_binetRatioDerivative_re z hz)
    apply ContinuousOn.log
    · fun_prop
    · intro u hu
      exact (one_sub_exp_two_pi_pos hu).ne'
  refine Integrable.mono' (g := fun u : ℝ => (3 / ‖z‖ + 18) *
    (-Real.log (1 - Real.exp (-(2 * Real.pi * u)))))
    (integrableOn_negLog_one_sub_exp.const_mul (3 / ‖z‖ + 18))
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hL : 0 ≤ -Real.log (1 - Real.exp (-(2 * Real.pi * u))) := neg_nonneg.mpr (binetLog_nonpos hu)
  have hN := binetRatioDerivative_tail_bound z hz hzy hn u
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (binetLog_nonpos hu)]
  exact mul_le_mul_of_nonneg_right hN hL

private lemma tendsto_binetRatio_mul_log_atTop (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hzy : z.re ^ 2 < z.im ^ 2) (hn : 4 ≤ ‖z‖) :
    Filter.Tendsto (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
      Real.log (1 - Real.exp (-(2 * Real.pi * u)))) Filter.atTop (nhds 0) := by
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivAt
      (fun t : ℝ => ((t : ℂ) / ((t : ℂ) ^ 2 + z ^ 2)).re *
        Real.log (1 - Real.exp (-(2 * Real.pi * t))))
      ((((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re *
          Real.log (1 - Real.exp (-(2 * Real.pi * u)))) +
        (((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
          (2 * Real.pi / (Real.exp (2 * Real.pi * u) - 1)))) u := by
    intro u hu
    exact (hasDerivAt_binetRatio_re z hz hu).mul (hasDerivAt_binetLog hu)
  have hdint : IntegrableOn (fun u : ℝ =>
      (((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re *
        Real.log (1 - Real.exp (-(2 * Real.pi * u)))) +
      (((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
        (2 * Real.pi / (Real.exp (2 * Real.pi * u) - 1)))) (Set.Ioi 0) :=
    (integrableOn_binetRatioDerivative_mul_log z hz hzy hn).add
      (integrableOn_binetRatio_mul_logDeriv z hz)
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hderiv hdint
    (integrableOn_binetRatio_mul_log z hz hzy hn)

private lemma tendsto_one_sub_exp_div :
    Filter.Tendsto (fun u : ℝ => (1 - Real.exp (-(2 * Real.pi * u))) / (2 * Real.pi * u))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hlin : HasDerivAt (fun t : ℝ => -(2 * Real.pi * t)) (-(2 * Real.pi)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-(2 * Real.pi))
  have hd := hlin.exp
  have hs := hd.tendsto_slope_zero_right
  simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, smul_eq_mul, one_mul] at hs
  have hm := hs.mul_const (-1 / (2 * Real.pi))
  convert hm using 1
  · ext u
    by_cases hu : u = 0
    · simp [hu]
    · field_simp [Real.pi_ne_zero, hu]
      simp [hu]
  · field_simp [Real.pi_ne_zero]

private lemma tendsto_binetRatio_div_re (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    Filter.Tendsto (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re / u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((z ^ 2)⁻¹.re)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hw0 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ 2 + z ^ 2) 0 := by fun_prop
  have hw : Filter.Tendsto (fun u : ℝ => (u : ℂ) ^ 2 + z ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (z ^ 2)) := by
    simpa using (hw0.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
  have hi := hw.inv₀ (pow_ne_zero 2 hz0)
  have hre := (Complex.continuous_re.tendsto ((z ^ 2)⁻¹)).comp hi
  apply hre.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hw0 := binet_denominator_ne z hz hu
  symm
  calc
    ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re / u =
      (((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)) / (u : ℂ)).re := by simp
    _ = (((u : ℂ) ^ 2 + z ^ 2)⁻¹).re := by
      congr 1
      field_simp

private lemma tendsto_binetRatio_mul_log_zero (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    Filter.Tendsto (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
      Real.log (1 - Real.exp (-(2 * Real.pi * u)))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hid : Filter.Tendsto (fun u : ℝ => u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Filter.Tendsto.mono_left Filter.tendsto_id nhdsWithin_le_nhds
  have hprod := (tendsto_binetRatio_div_re z hz).mul hid
  have hprod0 : Filter.Tendsto
      (fun u : ℝ => (((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re / u) * u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by simpa using hprod
  have hF : Filter.Tendsto (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    apply hprod0.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    field_simp [hu.out.ne']
  have hc0 : ContinuousAt (fun u : ℝ => 2 * Real.pi * u) 0 := by fun_prop
  have hc : Filter.Tendsto (fun u : ℝ => 2 * Real.pi * u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (hc0.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
  have hml := (Real.continuous_mul_log.tendsto 0).comp hc
  have hscaled := (tendsto_const_nhds (x := 1 / (2 * Real.pi))).mul hml
  have hml0 : Filter.Tendsto (fun u : ℝ => u * Real.log (2 * Real.pi * u))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    convert hscaled using 1
    · ext u
      simp only [Function.comp_def]
      field_simp [Real.pi_ne_zero]
    · simp
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp tendsto_one_sub_exp_div
  have hlog0 : Filter.Tendsto
      (fun u : ℝ => Real.log ((1 - Real.exp (-(2 * Real.pi * u))) / (2 * Real.pi * u)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Function.comp_def, Real.log_one] using hlog
  have hp1 := (tendsto_binetRatio_div_re z hz).mul hml0
  have hp2 := hF.mul hlog0
  have hsum := hp1.add hp2
  have hsum0 : Filter.Tendsto (fun x : ℝ =>
      ((x : ℂ) / ((x : ℂ) ^ 2 + z ^ 2)).re / x *
          (x * Real.log (2 * Real.pi * x)) +
        ((x : ℂ) / ((x : ℂ) ^ 2 + z ^ 2)).re *
          Real.log ((1 - Real.exp (-(2 * Real.pi * x))) / (2 * Real.pi * x)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [mul_zero, add_zero] using hsum
  apply hsum0.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : 0 < u := hu
  have hcpos : 0 < 2 * Real.pi * u := by positivity
  have hHpos : 0 < (1 - Real.exp (-(2 * Real.pi * u))) / (2 * Real.pi * u) :=
    div_pos (one_sub_exp_two_pi_pos hu) hcpos
  have hfactor : 1 - Real.exp (-(2 * Real.pi * u)) =
      (2 * Real.pi * u) * ((1 - Real.exp (-(2 * Real.pi * u))) / (2 * Real.pi * u)) := by
    field_simp [hu.out.ne', Real.pi_ne_zero]
  rw [hfactor, Real.log_mul hcpos.ne' hHpos.ne']
  field_simp [hu.out.ne']

private lemma binetRemainder_eq_integral (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hzy : z.re ^ 2 < z.im ^ 2) (hn : 4 ≤ ‖z‖) :
    binetRemainder z = (1 / Real.pi) *
      (∫ u : ℝ in Set.Ioi 0, ((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re *
        Real.log (1 - Real.exp (-(2 * Real.pi * u)))) := by
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => ((t : ℂ) / ((t : ℂ) ^ 2 + z ^ 2)).re)
    (u' := fun u : ℝ => ((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re)
    (v := fun u : ℝ => Real.log (1 - Real.exp (-(2 * Real.pi * u))))
    (v' := fun u : ℝ => 2 * Real.pi / (Real.exp (2 * Real.pi * u) - 1))
    (a := 0) (a' := 0) (b' := 0)
    (fun u hu => hasDerivAt_binetRatio_re z hz hu)
    (fun u hu => hasDerivAt_binetLog hu)
    (integrableOn_binetRatio_mul_logDeriv z hz)
    (integrableOn_binetRatioDerivative_mul_log z hz hzy hn)
    (tendsto_binetRatio_mul_log_zero z hz)
    (tendsto_binetRatio_mul_log_atTop z hz hzy hn)
  unfold binetRemainder
  calc
    (∫ u : ℝ in Set.Ioi 0, binetKernel z u) =
        -(1 / Real.pi) * (∫ u : ℝ in Set.Ioi 0,
          ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
            (2 * Real.pi / (Real.exp (2 * Real.pi * u) - 1))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hk := binetRatio_mul_logDeriv z hz hu
      rw [hk]
      field_simp [Real.pi_ne_zero]
    _ = -(1 / Real.pi) * (-(∫ u : ℝ in Set.Ioi 0,
        ((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re *
          Real.log (1 - Real.exp (-(2 * Real.pi * u))))) := by rw [hIBP]; norm_num
    _ = (1 / Real.pi) * (∫ u : ℝ in Set.Ioi 0,
        ((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re *
          Real.log (1 - Real.exp (-(2 * Real.pi * u)))) := by ring

private lemma binetRemainder_large_bound (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hzy : z.re ^ 2 < z.im ^ 2) (hn : 4 ≤ ‖z‖) :
    binetRemainder z ≤ 15 / (128 * ‖z‖ ^ 2) +
      (3 / ‖z‖ + 18) * Real.exp (-(2 * Real.pi * (‖z‖ / 3))) / 12 := by
  have hr : 0 < ‖z‖ := by linarith
  have hR : 1 ≤ ‖z‖ / 3 := by linarith
  have hNint := integrableOn_binetRatioDerivative_mul_log z hz hzy hn
  have hAbsInt : IntegrableOn (fun u : ℝ =>
      |((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re| *
        (-Real.log (1 - Real.exp (-(2 * Real.pi * u))))) (Set.Ioi 0) := by
    have hnnorm := hNint.norm
    refine IntegrableOn.congr_fun hnnorm ?_ measurableSet_Ioi
    intro u hu
    simp [Real.norm_eq_abs, abs_mul, abs_of_nonpos (binetLog_nonpos hu)]
  have hcomp : (∫ u : ℝ in Set.Ioi 0,
      ((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re *
        Real.log (1 - Real.exp (-(2 * Real.pi * u)))) ≤
      ∫ u : ℝ in Set.Ioi 0,
      |((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re| *
        (-Real.log (1 - Real.exp (-(2 * Real.pi * u)))) := by
    apply integral_mono_ae hNint hAbsInt
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    calc
      ((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re *
          Real.log (1 - Real.exp (-(2 * Real.pi * u))) ≤
        |((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re *
          Real.log (1 - Real.exp (-(2 * Real.pi * u)))| := le_abs_self _
      _ = |((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re| *
          (-Real.log (1 - Real.exp (-(2 * Real.pi * u)))) := by
        rw [abs_mul, abs_of_nonpos (binetLog_nonpos hu)]
  have hmain : binetRemainder z ≤ (1 / Real.pi) *
      (∫ u : ℝ in Set.Ioi 0,
      |((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re| *
        (-Real.log (1 - Real.exp (-(2 * Real.pi * u))))) := by
    rw [binetRemainder_eq_integral z hz hzy hn]
    exact mul_le_mul_of_nonneg_left hcomp (by positivity)
  have hset : Set.Ioc (0 : ℝ) (‖z‖ / 3) ∪ Set.Ioi (‖z‖ / 3) = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi (by linarith)
  have hsplit := setIntegral_union (f := fun u : ℝ =>
      |((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re| *
        (-Real.log (1 - Real.exp (-(2 * Real.pi * u)))))
    Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hAbsInt.mono_set Set.Ioc_subset_Ioi_self)
    (hAbsInt.mono_set (Set.Ioi_subset_Ioi (show (0 : ℝ) ≤ ‖z‖ / 3 by linarith)))
  rw [hset] at hsplit
  have hlow := integral_mono_ae (hAbsInt.mono_set Set.Ioc_subset_Ioi_self)
    (IntegrableOn.mono_set (integrableOn_negLog_one_sub_exp.const_mul (45 / (32 * ‖z‖ ^ 2)))
      Set.Ioc_subset_Ioi_self)
    (show (fun u : ℝ => |((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re| *
        (-Real.log (1 - Real.exp (-(2 * Real.pi * u))))) ≤ᵐ[volume.restrict (Set.Ioc 0 (‖z‖ / 3))]
      (fun u => (45 / (32 * ‖z‖ ^ 2)) * (-Real.log (1 - Real.exp (-(2 * Real.pi * u))))) by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hL : 0 ≤ -Real.log (1 - Real.exp (-(2 * Real.pi * u))) :=
        neg_nonneg.mpr (binetLog_nonpos hu.1)
      exact mul_le_mul_of_nonneg_right (binetRatioDerivative_low_bound z hn hu.1 hu.2) hL)
  rw [integral_const_mul] at hlow
  have hLset := setIntegral_union (f := fun u : ℝ => -Real.log (1 - Real.exp (-(2 * Real.pi * u))))
    Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (integrableOn_negLog_one_sub_exp.mono_set Set.Ioc_subset_Ioi_self)
    (integrableOn_negLog_one_sub_exp.mono_set (Set.Ioi_subset_Ioi (show (0 : ℝ) ≤ ‖z‖ / 3 by linarith)))
  rw [hset] at hLset
  have hLtail_nonneg : 0 ≤ ∫ u : ℝ in Set.Ioi (‖z‖ / 3),
      -Real.log (1 - Real.exp (-(2 * Real.pi * u))) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact neg_nonneg.mpr (binetLog_nonpos (by linarith [hu.out] : 0 < u))
  have hLlow : (∫ u : ℝ in Set.Ioc 0 (‖z‖ / 3),
      -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) ≤ Real.pi / 12 := by
    calc
      (∫ u : ℝ in Set.Ioc 0 (‖z‖ / 3), -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) ≤
          (∫ u : ℝ in Set.Ioc 0 (‖z‖ / 3), -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) +
          (∫ u : ℝ in Set.Ioi (‖z‖ / 3), -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) :=
        le_add_of_nonneg_right hLtail_nonneg
      _ = (∫ u : ℝ in Set.Ioi 0, -Real.log (1 - Real.exp (-(2 * Real.pi * u)))) := hLset.symm
      _ = Real.pi / 12 := integral_negLog_one_sub_exp
  have hlow2 := hlow.trans (mul_le_mul_of_nonneg_left hLlow (by positivity))
  have htail := integral_mono_ae (hAbsInt.mono_set (Set.Ioi_subset_Ioi (show (0 : ℝ) ≤ ‖z‖ / 3 by linarith)))
    (IntegrableOn.mono_set (integrableOn_negLog_one_sub_exp.const_mul (3 / ‖z‖ + 18))
      (Set.Ioi_subset_Ioi (show (0 : ℝ) ≤ ‖z‖ / 3 by linarith)))
    (show (fun u : ℝ => |((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re| *
        (-Real.log (1 - Real.exp (-(2 * Real.pi * u))))) ≤ᵐ[volume.restrict (Set.Ioi (‖z‖ / 3))]
      (fun u => (3 / ‖z‖ + 18) * (-Real.log (1 - Real.exp (-(2 * Real.pi * u))))) by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hL : 0 ≤ -Real.log (1 - Real.exp (-(2 * Real.pi * u))) :=
        neg_nonneg.mpr (binetLog_nonpos (by linarith [hu.out] : 0 < u))
      exact mul_le_mul_of_nonneg_right (binetRatioDerivative_tail_bound z hz hzy hn u) hL)
  rw [integral_const_mul] at htail
  have htail2 := htail.trans (mul_le_mul_of_nonneg_left
    (integral_negLog_one_sub_exp_tail_pi_le (show (0 : ℝ) ≤ ‖z‖ / 3 by linarith)) (by positivity))
  have hsum : (∫ u : ℝ in Set.Ioi 0,
      |((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2).re| *
        (-Real.log (1 - Real.exp (-(2 * Real.pi * u))))) ≤
      (45 / (32 * ‖z‖ ^ 2)) * (Real.pi / 12) +
        (3 / ‖z‖ + 18) * ((Real.pi / 12) * Real.exp (-(2 * Real.pi * (‖z‖ / 3)))) := by
    rw [hsplit]
    exact add_le_add hlow2 htail2
  refine hmain.trans ?_
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1 / Real.pi by positivity)
  convert hmul using 1 <;> field_simp [Real.pi_ne_zero] <;> ring

private lemma exp_neg_eight_pi_div_three_lt :
    Real.exp (-(8 * Real.pi / 3)) < 1 / 1000 := by
  have hp : 1000 < (Real.exp 1) ^ 8 := by
    calc
      1000 < (2.7182818283 : ℝ) ^ 8 := by norm_num
      _ ≤ (Real.exp 1) ^ 8 := by gcongr; exact Real.exp_one_gt_d9.le
  have he8 : 1000 < Real.exp 8 := by
    have heq : Real.exp (8 : ℝ) = (Real.exp 1) ^ 8 := by
      calc
        Real.exp (8 : ℝ) = Real.exp (((8 : ℕ) : ℝ) * 1) := by congr 1; norm_num
        _ = (Real.exp 1) ^ 8 := Real.exp_nat_mul 1 8
    rw [heq]
    exact hp
  have he : 1000 < Real.exp (8 * Real.pi / 3) := by
    exact he8.trans (Real.exp_lt_exp.mpr (by nlinarith [Real.pi_gt_three]))
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num) he

private lemma exp_neg_eight_pi_div_three_lt_four_thousand :
    Real.exp (-(8 * Real.pi / 3)) < 1 / 4000 := by
  have hp : 2800 < (Real.exp 1) ^ 8 := by
    calc
      2800 < (2.7182818283 : ℝ) ^ 8 := by norm_num
      _ ≤ (Real.exp 1) ^ 8 := by gcongr; exact Real.exp_one_gt_d9.le
  have heq8 : Real.exp (8 : ℝ) = (Real.exp 1) ^ 8 := by
    calc
      Real.exp (8 : ℝ) = Real.exp (((8 : ℕ) : ℝ) * 1) := by congr 1; norm_num
      _ = (Real.exp 1) ^ 8 := Real.exp_nat_mul 1 8
  have hd : 28 / 75 < 8 * Real.pi / 3 - 8 := by nlinarith [Real.pi_gt_d2]
  have hbase : 10 / 7 < (1 + (8 * Real.pi / 3 - 8) / 4) ^ 4 := by
    calc
      10 / 7 < (1 + (28 / 75) / 4) ^ 4 := by norm_num
      _ ≤ (1 + (8 * Real.pi / 3 - 8) / 4) ^ 4 := by gcongr
  have hfac : 10 / 7 < Real.exp (8 * Real.pi / 3 - 8) := by
    refine hbase.trans_le ?_
    have hadd := Real.add_one_le_exp ((8 * Real.pi / 3 - 8) / 4)
    have hpow : (1 + (8 * Real.pi / 3 - 8) / 4) ^ 4 ≤
        (Real.exp ((8 * Real.pi / 3 - 8) / 4)) ^ 4 := by
      apply pow_le_pow_left₀ (by positivity) _ 4
      simpa [add_comm] using hadd
    calc
      (1 + (8 * Real.pi / 3 - 8) / 4) ^ 4 ≤
          (Real.exp ((8 * Real.pi / 3 - 8) / 4)) ^ 4 := hpow
      _ = Real.exp (8 * Real.pi / 3 - 8) := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
        ring
  have hm1 := mul_le_mul_of_nonneg_left hp.le (show 0 ≤ 10 / 7 by norm_num)
  have hm2 := mul_le_mul_of_nonneg_right hfac.le (show 0 ≤ (Real.exp 1) ^ 8 by positivity)
  have hx : 4000 < (Real.exp 1) ^ 8 * Real.exp (8 * Real.pi / 3 - 8) := by
    nlinarith
  have he : 4000 < Real.exp (8 * Real.pi / 3) := by
    calc
      4000 < (Real.exp 1) ^ 8 * Real.exp (8 * Real.pi / 3 - 8) := hx
      _ = Real.exp 8 * Real.exp (8 * Real.pi / 3 - 8) := by rw [heq8]
      _ = Real.exp (8 + (8 * Real.pi / 3 - 8)) := by rw [Real.exp_add]
      _ = Real.exp (8 * Real.pi / 3) := by congr 1; ring
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num) he

private lemma mul_exp_neg_two_pi_div_three_le_four {r : ℝ} (hr : 4 ≤ r) :
    r * Real.exp (-(2 * Real.pi * r / 3)) ≤ 4 * Real.exp (-(8 * Real.pi / 3)) := by
  have he : r / 4 ≤ Real.exp ((2 * Real.pi / 3) * (r - 4)) := by
    calc
      r / 4 ≤ 1 + (2 * Real.pi / 3) * (r - 4) := by nlinarith [Real.pi_gt_three]
      _ ≤ Real.exp ((2 * Real.pi / 3) * (r - 4)) := by
        simpa [add_comm] using Real.add_one_le_exp ((2 * Real.pi / 3) * (r - 4))
  have hpos : 0 < Real.exp ((2 * Real.pi / 3) * (r - 4)) := Real.exp_pos _
  have hm := mul_le_mul_of_nonneg_right he
    (show 0 ≤ 4 * Real.exp (-(8 * Real.pi / 3)) / Real.exp ((2 * Real.pi / 3) * (r - 4)) by positivity)
  have hid : Real.exp (-(8 * Real.pi / 3)) / Real.exp ((2 * Real.pi / 3) * (r - 4)) =
      Real.exp (-(2 * Real.pi * r / 3)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  calc
    r * Real.exp (-(2 * Real.pi * r / 3)) =
        (r / 4) * (4 * Real.exp (-(8 * Real.pi / 3)) /
          Real.exp ((2 * Real.pi / 3) * (r - 4))) := by rw [← hid]; ring
    _ ≤ Real.exp ((2 * Real.pi / 3) * (r - 4)) *
        (4 * Real.exp (-(8 * Real.pi / 3)) / Real.exp ((2 * Real.pi / 3) * (r - 4))) := hm
    _ = 4 * Real.exp (-(8 * Real.pi / 3)) := by field_simp

private lemma sq_mul_exp_neg_two_pi_div_three_le_sixteen {r : ℝ} (hr : 4 ≤ r) :
    r ^ 2 * Real.exp (-(2 * Real.pi * r / 3)) ≤ 16 * Real.exp (-(8 * Real.pi / 3)) := by
  have hbase : r / 4 ≤ 1 + (Real.pi / 3) * (r - 4) := by nlinarith [Real.pi_gt_three]
  have he : r / 4 ≤ Real.exp ((Real.pi / 3) * (r - 4)) :=
    hbase.trans (by simpa [add_comm] using Real.add_one_le_exp ((Real.pi / 3) * (r - 4)))
  have hsq : (r / 4) ^ 2 ≤ (Real.exp ((Real.pi / 3) * (r - 4))) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (Real.exp_pos _).le).mpr he
  have heq : (Real.exp ((Real.pi / 3) * (r - 4))) ^ 2 =
      Real.exp ((2 * Real.pi / 3) * (r - 4)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [heq] at hsq
  have hm := mul_le_mul_of_nonneg_right hsq
    (show 0 ≤ 16 * Real.exp (-(8 * Real.pi / 3)) / Real.exp ((2 * Real.pi / 3) * (r - 4)) by positivity)
  have hid : Real.exp (-(8 * Real.pi / 3)) / Real.exp ((2 * Real.pi / 3) * (r - 4)) =
      Real.exp (-(2 * Real.pi * r / 3)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  calc
    r ^ 2 * Real.exp (-(2 * Real.pi * r / 3)) =
        (r / 4) ^ 2 * (16 * Real.exp (-(8 * Real.pi / 3)) /
          Real.exp ((2 * Real.pi / 3) * (r - 4))) := by rw [← hid]; ring
    _ ≤ Real.exp ((2 * Real.pi / 3) * (r - 4)) *
        (16 * Real.exp (-(8 * Real.pi / 3)) / Real.exp ((2 * Real.pi / 3) * (r - 4))) := hm
    _ = 16 * Real.exp (-(8 * Real.pi / 3)) := by field_simp

private lemma large_exp_tail_le {r : ℝ} (hr : 4 ≤ r) :
    (3 / r + 18) * Real.exp (-(2 * Real.pi * r / 3)) / 12 ≤ 1 / (160 * r ^ 2) := by
  have hr0 : 0 < r := by linarith
  have he0 := mul_exp_neg_two_pi_div_three_le_four hr
  have he0sq := sq_mul_exp_neg_two_pi_div_three_le_sixteen hr
  have hnum : (3 * r + 18 * r ^ 2) * Real.exp (-(2 * Real.pi * r / 3)) ≤
      300 * Real.exp (-(8 * Real.pi / 3)) := by
    have h3 := mul_le_mul_of_nonneg_left he0 (show 0 ≤ 3 by norm_num)
    have h18 := mul_le_mul_of_nonneg_left he0sq (show 0 ≤ 18 by norm_num)
    nlinarith
  calc
    (3 / r + 18) * Real.exp (-(2 * Real.pi * r / 3)) / 12 =
        ((3 * r + 18 * r ^ 2) * Real.exp (-(2 * Real.pi * r / 3))) / (12 * r ^ 2) := by
      field_simp [hr0.ne']
    _ ≤ (300 * Real.exp (-(8 * Real.pi / 3))) / (12 * r ^ 2) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (300 / 4000) / (12 * r ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have he0lt := exp_neg_eight_pi_div_three_lt_four_thousand
      nlinarith
    _ = 1 / (160 * r ^ 2) := by field_simp; ring

private lemma neg_one_div_two_mul_re_eq (z : ℂ) :
    -(1 / (2 * z)).re = -z.re / (2 * ‖z‖ ^ 2) := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : Complex.normSq (2 * z) = 4 * ‖z‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, norm_mul]
    norm_num
    ring
  rw [Complex.div_re, hn]
  simp only [Complex.one_re, Complex.one_im, zero_mul, add_zero]
  have hre : (2 * z).re = 2 * z.re := by simp
  rw [hre]
  field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)]
  ring

private lemma binetKernel_nonpos_of_im_sq_le {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re)
    (hzy : z.im ^ 2 ≤ z.re ^ 2) {u : ℝ} (hu : 0 < u) :
    binetKernel z u ≤ 0 := by
  have hD : 0 ≤ u ^ 2 + z.re ^ 2 - z.im ^ 2 := by nlinarith [sq_nonneg u]
  have hM : 0 ≤ (u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
    positivity
  have hE : 0 < Real.exp (2 * Real.pi * u) - 1 := exp_two_pi_mul_sub_one_pos hu
  unfold binetKernel
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (mul_nonneg hM hE.le)

private lemma binetRemainder_nonpos_of_im_sq_le {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re)
    (hzy : z.im ^ 2 ≤ z.re ^ 2) : binetRemainder z ≤ 0 := by
  unfold binetRemainder
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact binetKernel_nonpos_of_im_sq_le hz hzy hu

private lemma neg_one_div_two_mul_re_nonpos {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) :
    -(1 / (2 * z)).re ≤ 0 := by
  have hquot : 0 ≤ z.re / Complex.normSq z := div_nonneg (by linarith) (Complex.normSq_nonneg _)
  simpa [Complex.div_re] using (neg_nonpos.mpr hquot)

private lemma correction_nonpos_of_im_sq_le {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re)
    (hzy : z.im ^ 2 ≤ z.re ^ 2) :
    -(1 / (2 * z)).re + binetRemainder z ≤ 0 := by
  have hI := binetRemainder_nonpos_of_im_sq_le hz hzy
  have hone := neg_one_div_two_mul_re_nonpos hz
  linarith

/-- LEAF. Chandee Appendix page 12, first display and definition of I.
The cited formula is Ahlfors page 202. Integrability is explicit.
There is no sign estimate for the remainder in this leaf. -/
theorem binet_identity (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    IntegrableOn (binetKernel z) (Set.Ioi (0 : ℝ)) ∧
    (deriv Complex.Gamma z / Complex.Gamma z).re =
      Real.log ‖z‖ - (1 / (2 * z)).re + binetRemainder z := by
  sorry

/-- LEAF. Chandee Appendix pages 12 and 13, Case 1 and display 24.
The initial sign argument handles imaginary part squared at most real
part squared. Otherwise the integral split at norm z over three bounds
this correction on the unbounded region. There is no Gamma term. -/
theorem large_correction (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hn : 4 ≤ ‖z‖) :
    -(1 / (2 * z)).re + binetRemainder z ≤ 0 := by
  by_cases hzy : z.re ^ 2 < z.im ^ 2
  · rw [neg_one_div_two_mul_re_eq]
    have hB := binetRemainder_large_bound z hz hzy hn
    have hE := large_exp_tail_le hn
    have hr : 0 < ‖z‖ := by linarith
    have hlt : 15 / 128 + 1 / 160 < z.re / 2 := by
      norm_num
      linarith
    have hfrac : 15 / (128 * ‖z‖ ^ 2) + 1 / (160 * ‖z‖ ^ 2) < z.re / (2 * ‖z‖ ^ 2) := by
      calc
        15 / (128 * ‖z‖ ^ 2) + 1 / (160 * ‖z‖ ^ 2) =
            (15 / 128 + 1 / 160) / ‖z‖ ^ 2 := by ring
        _ < (z.re / 2) / ‖z‖ ^ 2 := by
          apply (div_lt_div_iff₀ (by positivity : 0 < ‖z‖ ^ 2)
            (by positivity : 0 < ‖z‖ ^ 2)).mpr
          exact mul_lt_mul_of_pos_right hlt (by positivity)
        _ = z.re / (2 * ‖z‖ ^ 2) := by ring
    simp only [mul_div_assoc] at hB hE
    have hI : binetRemainder z ≤ 15 / (128 * ‖z‖ ^ 2) + 1 / (160 * ‖z‖ ^ 2) := by
      linarith
    have hb : binetRemainder z < z.re / (2 * ‖z‖ ^ 2) := lt_of_le_of_lt hI hfrac
    convert (sub_neg_of_lt hb).le using 1 <;> ring
  · exact correction_nonpos_of_im_sq_le hz (le_of_not_gt hzy)

/-- LEAF. Chandee Appendix page 13, Case 2 and its final display.
The bounded region reduces to f at real part one quarter, followed by
the stated numerical verification. That input remains OPEN. The initial
sign argument handles the remaining imaginary parts. -/
theorem small_correction (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hn : ‖z‖ < 4) :
    -(1 / (2 * z)).re + binetRemainder z ≤ 0 := by
  sorry

/-- Chandee Lemma 2.3 from its three smaller Appendix inputs.
CONDITIONAL ON the Binet identity and the two remainder regions. -/
theorem gamma_log_derivative (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    (deriv Complex.Gamma z / Complex.Gamma z).re ≤ Real.log ‖z‖ := by
  rw [(binet_identity z hz).2]
  by_cases hn : 4 ≤ ‖z‖
  · linarith [large_correction z hz hn]
  · linarith [small_correction z hz (lt_of_not_ge hn)]

/-- P0075 page 4, chain-rule factor in the inherited composed-Gamma target. -/
theorem gamma_chain (s : ℂ) (hs : 0 ≤ s.re) :
    (deriv (fun z => Complex.Gamma (z / 2 + 1)) s / Complex.Gamma (s / 2 + 1)).re =
      (1 / 2 : ℝ) * (deriv Complex.Gamma (s / 2 + 1) / Complex.Gamma (s / 2 + 1)).re := by
  have hw : 0 < (s / 2 + 1).re := by simp [Complex.div_re]; linarith
  have hp : ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
    intro m hm
    have h := congrArg Complex.re hm
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hg : HasDerivAt (fun z : ℂ => z / 2 + 1) (1 / 2) s := by
    convert ((hasDerivAt_id s).div_const (2 : ℂ)).add_const 1 using 1 <;> simp
  have h := hg.logDeriv_Gamma hp
  simp only [logDeriv_apply, Complex.digamma_def] at h
  rw [h]
  simp [Complex.mul_re]

/-- P0075 page 4, elementary logarithm bound for the shifted argument. -/
theorem shifted_log_norm (s : ℂ) (hs : 0 ≤ s.re) (ht : s.im ≠ 0) :
    Real.log ‖s / 2 + 1‖ ≤ Real.log |s.im| - Real.log 2 +
      (s.re + 2) ^ 2 / (2 * s.im ^ 2) := by
  let w : ℂ := s / 2 + 1
  have hwre : 1 ≤ w.re := by simp [w, Complex.div_re]; linarith
  have hwn : 1 ≤ ‖w‖ := hwre.trans (Complex.re_le_norm w)
  have hw0 : 0 < ‖w‖ := by linarith
  have hn : ‖w‖ ^ 2 = ((s.re + 2) ^ 2 + s.im ^ 2) / 4 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [w, Complex.div_re, Complex.div_im]
    ring
  have ht2 : s.im ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have h := Real.log_le_sub_one_of_pos
    (by positivity : 0 < 4 * ‖w‖ ^ 2 / s.im ^ 2)
  have he : 4 * ‖w‖ ^ 2 / s.im ^ 2 - 1 = (s.re + 2) ^ 2 / s.im ^ 2 := by
    rw [hn]
    field_simp
    ring
  have hl : Real.log (4 * ‖w‖ ^ 2 / s.im ^ 2) =
      2 * Real.log 2 + 2 * Real.log ‖w‖ - 2 * Real.log s.im := by
    rw [Real.log_div (by positivity) ht2,
      Real.log_mul (by norm_num) (pow_ne_zero 2 hw0.ne'), Real.log_pow, Real.log_pow,
      show Real.log (4 : ℝ) = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num]
    norm_num
  rw [he, hl] at h
  change Real.log ‖w‖ ≤ _
  rw [Real.log_abs]
  have hdiv : (s.re + 2) ^ 2 / (2 * s.im ^ 2) = ((s.re + 2) ^ 2 / s.im ^ 2) / 2 := by ring
  rw [hdiv]
  linarith

/-- P0075 page 4, exact statement of DecompJ966.leaf_gamma_bound.
CONDITIONAL ON the three Chandee Appendix leaves. The inherited target
uses a composed derivative, so its factor one half is retained. -/
theorem leaf_gamma_bound (s : ℂ) (h_re : s.re ≥ 0) (h_im : s.im ≠ 0) :
    (deriv (fun z => Complex.Gamma (z / 2 + 1)) s / Complex.Gamma (s / 2 + 1)).re ≤
    Real.log |s.im| - Real.log 2 + (s.re + 2) ^ 2 / (2 * s.im ^ 2) := by
  have hr : 1 ≤ (s / 2 + 1).re := by simp [Complex.div_re]; linarith
  have hn : 1 ≤ ‖s / 2 + 1‖ := hr.trans (Complex.re_le_norm _)
  have hl : 0 ≤ Real.log ‖s / 2 + 1‖ := Real.log_nonneg hn
  have hg := gamma_log_derivative (s / 2 + 1) (by linarith)
  rw [gamma_chain s h_re]
  apply le_trans (show (1 / 2 : ℝ) *
    (deriv Complex.Gamma (s / 2 + 1) / Complex.Gamma (s / 2 + 1)).re ≤
      Real.log ‖s / 2 + 1‖ by linarith)
  exact shifted_log_norm s h_re h_im

end LeanLab.ChirreHagen2025.Decomp377d

/-! Axiom audit for the leaves closed by the file's own proofs, and for the helpers above. -/
#print axioms LeanLab.ChirreHagen2025.Decomp377d.gamma_chain
#print axioms LeanLab.ChirreHagen2025.Decomp377d.shifted_log_norm
#print axioms LeanLab.ChirreHagen2025.Decomp377d.gamma_log_derivative
#print axioms LeanLab.ChirreHagen2025.Decomp377d.leaf_gamma_bound
#print axioms LeanLab.ChirreHagen2025.Decomp377d.binet_identity
#print axioms LeanLab.ChirreHagen2025.Decomp377d.large_correction
#print axioms LeanLab.ChirreHagen2025.Decomp377d.small_correction
