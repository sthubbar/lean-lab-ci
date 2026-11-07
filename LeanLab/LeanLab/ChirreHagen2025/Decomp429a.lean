import LeanLab.ChirreHagen2025.Decomp377d
import LeanLab.ChirreHagen2025.GammaGeometry429
import LeanLab.ChirreHagen2025.LogKernel429

/-!
P0075 page 4 and Chandee Appendix pages 12 and 13, display 24.
https://arxiv.org/abs/0906.4177
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp429a
open MeasureTheory Decomp377d

/-- Chandee page 12, the preliminary sign region before Case 1. -/
theorem kernel_nonpos (z : ℂ) (u : ℝ) (hu : 0 < u)
    (hxy : z.im ^ 2 ≤ z.re ^ 2) : binetKernel z u ≤ 0 := by
  unfold binetKernel
  apply div_nonpos_of_nonpos_of_nonneg
  · have : 0 ≤ u ^ 2 + z.re ^ 2 - z.im ^ 2 := by nlinarith [sq_nonneg u]
    nlinarith
  · have he : 0 ≤ Real.exp (2 * Real.pi * u) - 1 := by
      have := Real.one_le_exp (show 0 ≤ 2 * Real.pi * u by positivity)
      linarith
    positivity

/-- Chandee page 12, the preliminary sign argument for the full correction. -/
theorem correction_nonpos_of_im_sq_le (z : ℂ) (hz : 0 ≤ z.re)
    (hxy : z.im ^ 2 ≤ z.re ^ 2) :
    -(1 / (2 * z)).re + binetRemainder z ≤ 0 := by
  have hi : binetRemainder z ≤ 0 := by
    apply setIntegral_nonpos measurableSet_Ioi
    intro u hu
    exact kernel_nonpos z u hu hxy
  have hr : 0 ≤ (1 / (2 * z)).re := by
    norm_num [Complex.div_re, Complex.normSq_mul]
    exact mul_nonneg hz (inv_nonneg.mpr (Complex.normSq_nonneg z))
  linarith

/-- Chandee page 13, the scalar last inequality after display 24. -/
theorem exponential_absorption (r : ℝ) (hr : 4 ≤ r) :
    15 / (128 * r ^ 2) +
      4 * Real.exp (-2 * Real.pi * r / 3) / 3 * (1 + 1 / r ^ 2) ≤
      1 / (8 * r ^ 2) := by
  have hr0 : 0 < r := by linarith
  have hbase : (512 / 3 * 17 : ℝ) ≤ Real.exp 8 := by
    calc
      (512 / 3 * 17 : ℝ) ≤ (2.718 : ℝ) ^ 8 := by norm_num
      _ ≤ Real.exp 1 ^ 8 := by
        gcongr
        linarith [Real.exp_one_gt_d9]
      _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; norm_num
  have hlin : r - 3 ≤ Real.exp (r - 4) := by
    linarith [Real.add_one_le_exp (r - 4)]
  have hsq := pow_le_pow_left₀ (show 0 ≤ r - 3 by linarith) hlin 2
  have hpoly : r ^ 2 + 1 ≤ 17 * (r - 3) ^ 2 := by
    nlinarith [sq_nonneg (r - 4)]
  have hexp : (512 / 3 : ℝ) * (r ^ 2 + 1) ≤ Real.exp (2 * Real.pi * r / 3) := by
    calc
      _ ≤ (512 / 3 * 17) * (r - 3) ^ 2 := by nlinarith
      _ ≤ Real.exp 8 * Real.exp (r - 4) ^ 2 :=
        mul_le_mul hbase hsq (sq_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * r) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  have he0 : 0 < Real.exp (2 * Real.pi * r / 3) := Real.exp_pos _
  rw [show -2 * Real.pi * r / 3 = -(2 * Real.pi * r / 3) by ring,
    Real.exp_neg]
  apply (le_div_iff₀ (show 0 < 8 * r ^ 2 by positivity)).mpr
  field_simp
  rw [show r * 2 * Real.pi / 3 = 2 * Real.pi * r / 3 by ring]
  nlinarith

/-- Chandee page 13, the nonnegative integrand after integration by parts. -/
noncomputable def partsKernel (z : ℂ) (u : ℝ) : ℝ :=
  ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 *
    Real.log (1 / (1 - Real.exp (-2 * Real.pi * u)))

/-! ### Helpers for the two leaves -/

/-- Norm-square expansion of `u^2 + z^2`. -/
private lemma normSq_add_sq (z : ℂ) (u : ℝ) :
    ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 =
      (u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

/-- `‖z‖^2 = z.re^2 + z.im^2`. -/
private lemma norm_sq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- Elementary reciprocal identity. -/
private lemma one_div_one_sub_sub_one {r : ℝ} (hr : r < 1) :
    1 / (1 - r) - 1 = r / (1 - r) := by
  have h : 1 - r ≠ 0 := by linarith
  field_simp
  ring

/-- `8 ≤ exp 3`. -/
private lemma exp_three_ge_eight : (8 : ℝ) ≤ Real.exp 3 := by
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h]
  have h2 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 3
  linarith

/-- `log 8 ≤ 3`. -/
private lemma log_eight_le_three : Real.log 8 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  exact exp_three_ge_eight

/-- The logarithm kernel decays like twice the exponential. -/
private lemma logKernel_le_two_exp {u : ℝ} (hu : (1 / 2 : ℝ) ≤ u) :
    LogKernel429.logKernel u ≤ 2 * Real.exp (-2 * Real.pi * u) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hepos : (0 : ℝ) < Real.exp (-2 * Real.pi * u) := Real.exp_pos _
  have hexp_half : Real.exp (-2 * Real.pi * u) ≤ 1 / 2 := by
    have hle : -2 * Real.pi * u ≤ -Real.log 2 := by
      have h2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      have h3 : (1 : ℝ) ≤ 2 * Real.pi * u := by nlinarith
      linarith
    calc Real.exp (-2 * Real.pi * u) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr hle
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]
        norm_num
  have hrpos : 0 < 1 - Real.exp (-2 * Real.pi * u) := by linarith
  have hpos : 0 < 1 / (1 - Real.exp (-2 * Real.pi * u)) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hfrac : 1 / (1 - Real.exp (-2 * Real.pi * u)) - 1 =
      Real.exp (-2 * Real.pi * u) / (1 - Real.exp (-2 * Real.pi * u)) :=
    one_div_one_sub_sub_one (by linarith)
  have hge : (1 / 2 : ℝ) ≤ 1 - Real.exp (-2 * Real.pi * u) := by linarith
  have hprod : Real.exp (-2 * Real.pi * u) ≤
      2 * Real.exp (-2 * Real.pi * u) * (1 - Real.exp (-2 * Real.pi * u)) := by
    nlinarith [mul_nonneg hepos.le
      (show (0:ℝ) ≤ 1 - 2 * Real.exp (-2 * Real.pi * u) by linarith)]
  have hfin : Real.exp (-2 * Real.pi * u) / (1 - Real.exp (-2 * Real.pi * u)) ≤
      2 * Real.exp (-2 * Real.pi * u) := by
    rw [div_le_iff₀ hrpos]
    linarith
  unfold LogKernel429.logKernel
  linarith

/-- The logarithmic kernel is integrable past any positive point, with the
exponential tail bound. -/
private lemma tail_phi_integral {c : ℝ} (hc : (1 / 2 : ℝ) ≤ c) :
    ∫ u in Set.Ioi c, LogKernel429.logKernel u ≤
      Real.exp (-2 * Real.pi * c) / Real.pi := by
  have hφ : IntegrableOn LogKernel429.logKernel (Set.Ioi c) :=
    LogKernel429.log_kernel_integrable.mono_set (Set.Ioi_subset_Ioi (by linarith))
  have hg : IntegrableOn (fun u : ℝ => 2 * Real.exp (-2 * Real.pi * u)) (Set.Ioi c) := by
    have h := integrableOn_exp_mul_Ioi (a := -(2 * Real.pi)) (by nlinarith [Real.pi_pos]) c
    have h3 : (fun u : ℝ => 2 * Real.exp (-2 * Real.pi * u)) =
        (fun u : ℝ => 2 * Real.exp ((-(2 * Real.pi)) * u)) := by
      funext u
      rw [neg_mul]
    rw [h3]
    exact h.const_mul 2
  have hmono : ∫ u in Set.Ioi c, LogKernel429.logKernel u ≤
      ∫ u in Set.Ioi c, 2 * Real.exp (-2 * Real.pi * u) :=
    setIntegral_mono_on hφ hg measurableSet_Ioi
      (fun u hu => logKernel_le_two_exp (le_of_lt (lt_of_le_of_lt hc hu)))
  have hval : ∫ u in Set.Ioi c, 2 * Real.exp (-2 * Real.pi * u) =
      Real.exp (-2 * Real.pi * c) / Real.pi := by
    have hI := integral_exp_mul_Ioi (a := -(2 * Real.pi)) (by nlinarith [Real.pi_pos]) c
    have hcongr : (fun u : ℝ => Real.exp (-2 * Real.pi * u)) =
        (fun u : ℝ => Real.exp ((-(2 * Real.pi)) * u)) := by
      funext u
      rw [neg_mul]
    have h2 : ∫ u in Set.Ioi c, 2 * Real.exp (-2 * Real.pi * u) =
        2 * ∫ u in Set.Ioi c, Real.exp (-2 * Real.pi * u) := integral_const_mul 2 _
    rw [h2, hcongr, hI]
    have harg : -(2 * Real.pi) * c = -2 * Real.pi * c := by ring
    rw [harg]
    rw [show -Real.exp (-2 * Real.pi * c) / -(2 * Real.pi) =
      Real.exp (-2 * Real.pi * c) / (2 * Real.pi) by
        rw [show -(2 * Real.pi) = -(2 * Real.pi) from rfl, neg_div_neg_eq]]
    rw [show 2 * (Real.exp (-2 * Real.pi * c) / (2 * Real.pi)) =
      Real.exp (-2 * Real.pi * c) / Real.pi by
        have hp : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp]
  linarith

/-- Denominator lower bound in the folded region: at most `‖z‖^2/4` in `u^2`. -/
private lemma D_lower_half (z : ℂ) {u : ℝ} (hu : u ^ 2 ≤ ‖z‖ ^ 2 / 4) :
    ‖z‖ ^ 4 / 2 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
  have hR2 := norm_sq_re_im z
  have h4 : ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
  have heq : ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 =
      u ^ 4 + 2 * u ^ 2 * (z.re ^ 2 - z.im ^ 2) + ‖z‖ ^ 4 := by
    rw [normSq_add_sq, h4, hR2]
    ring
  have hk : -(‖z‖ ^ 2) ≤ z.re ^ 2 - z.im ^ 2 := by
    rw [hR2]; nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have h1 : 2 * u ^ 2 * (-(‖z‖ ^ 2)) ≤ 2 * u ^ 2 * (z.re ^ 2 - z.im ^ 2) :=
    mul_le_mul_of_nonneg_left hk (by positivity)
  have h2 : 2 * u ^ 2 * ‖z‖ ^ 2 ≤ ‖z‖ ^ 4 / 2 := by
    have hm := mul_le_mul_of_nonneg_left hu (by positivity : (0:ℝ) ≤ 2 * ‖z‖ ^ 2)
    have hsimp : 2 * ‖z‖ ^ 2 * (‖z‖ ^ 2 / 4) = ‖z‖ ^ 4 / 2 := by ring
    rw [hsimp] at hm
    linarith
  nlinarith [sq_nonneg (u ^ 2)]

/-- Denominator lower bound past the quadratic scale. -/
private lemma D_lower_u (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (u : ℝ) :
    u ^ 2 / 4 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
  have hR2 := norm_sq_re_im z
  have heq : ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 = (u ^ 2 - ‖z‖ ^ 2) ^ 2 + 4 * z.re ^ 2 * u ^ 2 := by
    rw [normSq_add_sq, hR2]
    ring
  have ha2 : (1 / 4 : ℝ) ≤ 4 * z.re ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ha2 (sq_nonneg u)
  nlinarith [sq_nonneg (u ^ 2 - ‖z‖ ^ 2)]

/-- Numerator upper bound. -/
private lemma num_le (z : ℂ) (u : ℝ) :
    ‖z ^ 2 - (u : ℂ) ^ 2‖ ≤ ‖z‖ ^ 2 + u ^ 2 := by
  have h := norm_sub_le (z ^ 2) ((u : ℂ) ^ 2)
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  linarith

/-- Folded-region ratio bound. -/
private lemma ratio_head_le (z : ℂ) {u : ℝ} (hu0 : 0 < u) (hu : u ≤ ‖z‖ / 2) :
    ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 ≤ 5 / (2 * ‖z‖ ^ 2) := by
  have hu2 : u ^ 2 ≤ ‖z‖ ^ 2 / 4 := by
    have h := pow_le_pow_left₀ hu0.le hu 2
    nlinarith
  have hRpos : (0 : ℝ) < ‖z‖ := by
    have h : (0:ℝ) < u ^ 2 := by positivity
    nlinarith
  have hnum := num_le z u
  have hden := D_lower_half z hu2
  have hdenpos : (0 : ℝ) < ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
    have h4 : (0:ℝ) < ‖z‖ ^ 4 := by positivity
    linarith
  rw [div_le_iff₀ hdenpos]
  have hstep : (5 : ℝ) / (2 * ‖z‖ ^ 2) * (‖z‖ ^ 4 / 2) ≤
      (5 : ℝ) / (2 * ‖z‖ ^ 2) * ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hden (by positivity)
  have h5 : (5 : ℝ) / (2 * ‖z‖ ^ 2) * (‖z‖ ^ 4 / 2) = 5 * ‖z‖ ^ 2 / 4 := by
    field_simp
    ring
  rw [h5] at hstep
  nlinarith

/-- Tail-region ratio bound. -/
private lemma ratio_tail_le (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) {u : ℝ}
    (hu : ‖z‖ / 2 ≤ u) :
    ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 ≤ 20 := by
  have hnum := num_le z u
  have hden := D_lower_u z hz u
  have hdenpos : (0 : ℝ) < ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
    have hRpos : (0:ℝ) < ‖z‖ := lt_of_lt_of_le (by norm_num) (le_trans hz (Complex.re_le_norm z))
    have hu0 : (0:ℝ) < u := lt_of_lt_of_le (by linarith) hu
    have h4 : (0:ℝ) < u ^ 2 / 4 := by positivity
    linarith
  rw [div_le_iff₀ hdenpos]
  have hu4 : ‖z‖ ^ 2 ≤ 4 * u ^ 2 := by
    have h0 : (0:ℝ) ≤ ‖z‖ / 2 := by positivity
    have h : (‖z‖ / 2) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ h0 hu 2
    nlinarith
  nlinarith

/-- Integrability of the parts kernel on the initial piece. -/
private lemma parts_integrable_head (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hn : 4 ≤ ‖z‖) :
    IntegrableOn (partsKernel z) (Set.Ioc 0 (‖z‖ / 3)) := by
  let C : ℝ := 45 / (32 * ‖z‖ ^ 2)
  have hz0 : z ≠ 0 := by
    intro he
    norm_num [he] at hn
  have hsub : Set.Ioc (0 : ℝ) (‖z‖ / 3) ⊆ Set.Ioi 0 := by
    intro u hu
    exact hu.1
  have hi := (LogKernel429.log_kernel_integrable.mono_set hsub).const_mul C
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioc (0 : ℝ) (‖z‖ / 3)) :
      partsKernel z u ≤ C * LogKernel429.logKernel u := by
    have hh := mul_le_mul_of_nonneg_right
      (GammaGeometry429.head_norm_ratio z hz0 u hu.1.le hu.2)
      (LogKernel429.log_kernel_nonneg u hu.1)
    simpa only [partsKernel, LogKernel429.logKernel, C] using hh
  have hnonneg (u : ℝ) (hu : 0 < u) : 0 ≤ partsKernel z u := by
    have hh := LogKernel429.log_kernel_nonneg u hu
    change 0 ≤ _ * LogKernel429.logKernel u
    positivity
  have hm : Measurable (partsKernel z) := by
    unfold partsKernel
    fun_prop
  exact hi.mono' hm.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u hu.1)]
    exact hpoint u hu)

/-- Integrability of the parts kernel on the tail. -/
private lemma parts_integrable_tail (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hn : 4 ≤ ‖z‖) :
    IntegrableOn (partsKernel z) (Set.Ioi (‖z‖ / 3)) := by
  have hR3 : (0 : ℝ) < ‖z‖ / 3 := by
    have h : (0:ℝ) < ‖z‖ := by linarith
    linarith
  have hR2p : (0 : ℝ) < ‖z‖ / 2 := by linarith
  have hle : ‖z‖ / 3 ≤ ‖z‖ / 2 := by linarith
  have hm : Measurable (partsKernel z) := by
    unfold partsKernel
    fun_prop
  have hnonneg : ∀ u : ℝ, 0 < u → 0 ≤ partsKernel z u := by
    intro u hu
    have hh := LogKernel429.log_kernel_nonneg u hu
    change 0 ≤ _ * LogKernel429.logKernel u
    positivity
  have hb1 : ∀ u ∈ Set.Ioc (‖z‖ / 3) (‖z‖ / 2),
      partsKernel z u ≤ (5 / (2 * ‖z‖ ^ 2)) * LogKernel429.logKernel u := by
    intro u hu
    have hu0 : 0 < u := lt_trans hR3 hu.1
    have hratio := ratio_head_le z hu0 hu.2
    have hφ := LogKernel429.log_kernel_nonneg u hu0
    have hfe : partsKernel z u =
        ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 * LogKernel429.logKernel u := rfl
    rw [hfe]
    exact mul_le_mul_of_nonneg_right hratio hφ
  have hb2 : ∀ u ∈ Set.Ioi (‖z‖ / 2),
      partsKernel z u ≤ 20 * LogKernel429.logKernel u := by
    intro u hu
    have hu0 : 0 < u := lt_trans hR2p hu
    have hratio := ratio_tail_le z hz hu.le
    have hφ := LogKernel429.log_kernel_nonneg u hu0
    have hfe : partsKernel z u =
        ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 * LogKernel429.logKernel u := rfl
    rw [hfe]
    exact mul_le_mul_of_nonneg_right hratio hφ
  have hdom1 : IntegrableOn (fun u : ℝ => (5 / (2 * ‖z‖ ^ 2)) * LogKernel429.logKernel u)
      (Set.Ioc (‖z‖ / 3) (‖z‖ / 2)) :=
    (LogKernel429.log_kernel_integrable.mono_set
      (by intro u hu; exact lt_trans hR3 hu.1)).const_mul _
  have hdom2 : IntegrableOn (fun u : ℝ => 20 * LogKernel429.logKernel u)
      (Set.Ioi (‖z‖ / 2)) :=
    (LogKernel429.log_kernel_integrable.mono_set (Set.Ioi_subset_Ioi hR2p.le)).const_mul _
  have hp1 : IntegrableOn (partsKernel z) (Set.Ioc (‖z‖ / 3) (‖z‖ / 2)) := by
    refine hdom1.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u (lt_trans hR3 hu.1))]
    exact hb1 u hu
  have hp2 : IntegrableOn (partsKernel z) (Set.Ioi (‖z‖ / 2)) := by
    refine hdom2.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u (lt_trans hR2p hu))]
    exact hb2 u hu
  rw [← Set.Ioc_union_Ioi_eq_Ioi hle]
  exact hp1.union hp2

/-! ### Ingredients of the integration by parts in `binet_split` -/

/-- Algebraic normal form of the logarithmic derivative factor. -/
private lemma pw_deriv_eq (E : ℝ) (hE : E < 1) :
    (-(2 * Real.pi * E) / (1 - E) ^ 2) / (1 - E)⁻¹ = -2 * Real.pi * E / (1 - E) := by
  have h : (1 - E) ≠ 0 := by linarith
  field_simp

/-- `exp (-pi u)` tends to zero at `+infinity`. -/
private lemma tendsto_exp_neg_pi_atTop :
    Filter.Tendsto (fun u : ℝ => Real.exp (-Real.pi * u)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun u : ℝ => -Real.pi * u) Filter.atTop Filter.atBot := by
    rw [Filter.tendsto_atBot]
    intro a
    refine Filter.eventually_atTop.2 ⟨a / (-Real.pi), fun u hu => ?_⟩
    have hp : (0:ℝ) < Real.pi := Real.pi_pos
    have h := mul_le_mul_of_nonpos_left hu (le_of_lt (by linarith : -Real.pi < 0))
    have h2 : -Real.pi * (a / (-Real.pi)) = a := by
      field_simp
    linarith [h, h2]
  exact Real.tendsto_exp_atBot.comp h

/-- The real part of `u / (u^2 + z^2)` in explicit real form. -/
private lemma Gw_eq (z : ℂ) (u : ℝ) :
    ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re =
      u * (u ^ 2 + z.re ^ 2 - z.im ^ 2) /
        ((u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2) := by
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have h1 : Complex.normSq ((u : ℂ) ^ 2 + z ^ 2) =
      (u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact normSq_add_sq z u
  have h2 : ((u : ℂ) ^ 2 + z ^ 2).re = u ^ 2 + z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two, Complex.add_re, Complex.mul_re]
    ring
  rw [h1, h2]
  simp

/-- The derivative's real part is dominated by the norm ratio. -/
private lemma Gw'_le (z : ℂ) (u : ℝ) :
    |(((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re| ≤
      ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
  have h1 : |(((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re| ≤
      ‖(z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2‖ :=
    Complex.abs_re_le_norm _
  rwa [norm_div, norm_pow] at h1

/-- `exp (-2 pi u)` rewritten with a negative exponent argument. -/
private lemma exp_neg_two_pi (u : ℝ) :
    Real.exp (-2 * Real.pi * u) = (Real.exp (2 * Real.pi * u))⁻¹ := by
  rw [show -2 * Real.pi * u = -(2 * Real.pi * u) by ring, Real.exp_neg]

/-- `1 - exp (-2 pi u)` dominates `pi u` below `1/8`. -/
private lemma one_sub_exp_ge {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 8) :
    Real.pi * u ≤ 1 - Real.exp (-2 * Real.pi * u) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hx0 : 0 < 2 * Real.pi * u := by positivity
  have hx1 : 2 * Real.pi * u ≤ 1 := by nlinarith
  have hpos : 0 < 1 + 2 * Real.pi * u := by linarith
  have hexp : 1 + 2 * Real.pi * u ≤ Real.exp (2 * Real.pi * u) := by
    linarith [Real.add_one_le_exp (2 * Real.pi * u)]
  have hinv : (Real.exp (2 * Real.pi * u))⁻¹ ≤ (1 + 2 * Real.pi * u)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) hpos).mpr hexp
  have hkey : (1 : ℝ) - (1 + 2 * Real.pi * u)⁻¹ =
      (2 * Real.pi * u) / (1 + 2 * Real.pi * u) := by
    rw [eq_div_iff hpos.ne']
    field_simp
    ring
  have h2 : Real.pi * u ≤ (2 * Real.pi * u) / (1 + 2 * Real.pi * u) := by
    rw [le_div_iff₀ hpos]
    nlinarith
  have h3 : (1 : ℝ) - (1 + 2 * Real.pi * u)⁻¹ ≤ 1 - (Real.exp (2 * Real.pi * u))⁻¹ := by
    linarith
  rw [exp_neg_two_pi]
  linarith

/-- `1 - exp (-2 pi u)` is at least `1/2` past `1/8`. -/
private lemma one_sub_exp_ge_half {u : ℝ} (hu : 1 / 8 ≤ u) :
    (1 / 2 : ℝ) ≤ 1 - Real.exp (-2 * Real.pi * u) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlog2 : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hle : -2 * Real.pi * u ≤ -Real.log 2 := by nlinarith
  have hexp : Real.exp (-2 * Real.pi * u) ≤ 1 / 2 := by
    calc Real.exp (-2 * Real.pi * u) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr hle
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]
        norm_num
  linarith

/-- `logKernel` is bounded by `log (1/(pi u))` below `1/8`. -/
private lemma logKernel_le_log_inv {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 8) :
    LogKernel429.logKernel u ≤ Real.log (1 / (Real.pi * u)) := by
  have hA := one_sub_exp_ge hu0 hu
  have hApos : 0 < 1 - Real.exp (-2 * Real.pi * u) := by
    have h : 0 < Real.pi * u := by positivity
    linarith
  have hpiu : 0 < Real.pi * u := by positivity
  have hle : 1 / (1 - Real.exp (-2 * Real.pi * u)) ≤ 1 / (Real.pi * u) := by
    rw [div_le_div_iff₀ hApos hpiu]
    linarith
  calc LogKernel429.logKernel u = Real.log (1 / (1 - Real.exp (-2 * Real.pi * u))) := rfl
    _ ≤ Real.log (1 / (Real.pi * u)) := Real.log_le_log (by positivity) hle

/-- `u * log (1/(pi u))` tends to zero at `0+`. -/
private lemma tendsto_mul_log_inv :
    Filter.Tendsto (fun u : ℝ => u * Real.log (1 / (Real.pi * u)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h1 : Filter.Tendsto (fun w : ℝ => Real.log w / w) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Filter.Tendsto (fun u : ℝ => u⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have h4 : Filter.Tendsto (fun u : ℝ => Real.log u⁻¹ / u⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := h1.comp h2
  have h5 : Filter.Tendsto (fun u : ℝ => u * Real.log Real.pi)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hid : Filter.Tendsto (fun u : ℝ => u) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      Filter.tendsto_id.mono_left nhdsWithin_le_nhds
    have h := hid.mul_const (Real.log Real.pi)
    simpa using h
  have h6 : Filter.Tendsto (fun u : ℝ => Real.log u⁻¹ / u⁻¹ - u * Real.log Real.pi)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using h4.sub h5
  refine h6.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hp0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hlog : Real.log (Real.pi * u) = Real.log Real.pi + Real.log u :=
    Real.log_mul hp0 hu0
  simp only [one_div, Real.log_inv, hlog]
  field_simp
  ring

/-- Uniform linear bound on the antiderivative's real part. -/
private lemma Gw_abs_le_lin (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hxy : z.re ^ 2 < z.im ^ 2)
    {u : ℝ} (hu : 0 ≤ u) :
    |((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re| ≤ 4 * u := by
  have ha : (0 : ℝ) < z.re := by linarith
  have ham : (1 / 4 : ℝ) < |z.im| := by
    have h1 : (1 / 4 : ℝ) ^ 2 < z.im ^ 2 := by nlinarith
    rw [sq_lt_sq, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at h1
    exact h1
  have hb2 : (1 / 16 : ℝ) < z.im ^ 2 := by
    rw [← sq_abs]
    nlinarith
  have ha2 : (1 / 16 : ℝ) ≤ z.re ^ 2 := by nlinarith
  have hprod : (1 / 16 : ℝ) * (1 / 16) ≤ z.re ^ 2 * z.im ^ 2 :=
    mul_le_mul ha2 (le_of_lt hb2) (by norm_num) (by nlinarith)
  have hm2 : (1 / 64 : ℝ) < 4 * z.re ^ 2 * z.im ^ 2 := by nlinarith
  have hm2pos : 0 < 4 * z.re ^ 2 * z.im ^ 2 := by linarith
  have hsqrt : (1 / 8 : ℝ) ≤ Real.sqrt (4 * z.re ^ 2 * z.im ^ 2) := by
    have h : Real.sqrt ((1 / 8 : ℝ) ^ 2) ≤ Real.sqrt (4 * z.re ^ 2 * z.im ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith : (1 / 8 : ℝ) ^ 2 ≤ 4 * z.re ^ 2 * z.im ^ 2)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 8)] at h
  have hD : 0 < (u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
    positivity
  have hAM : 2 * |u ^ 2 + z.re ^ 2 - z.im ^ 2| * Real.sqrt (4 * z.re ^ 2 * z.im ^ 2) ≤
      (u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
    have hsq : Real.sqrt (4 * z.re ^ 2 * z.im ^ 2) ^ 2 = 4 * z.re ^ 2 * z.im ^ 2 :=
      Real.sq_sqrt hm2pos.le
    nlinarith [sq_nonneg (|u ^ 2 + z.re ^ 2 - z.im ^ 2| - Real.sqrt (4 * z.re ^ 2 * z.im ^ 2)),
      sq_abs (u ^ 2 + z.re ^ 2 - z.im ^ 2),
      abs_nonneg (u ^ 2 + z.re ^ 2 - z.im ^ 2)]
  rw [Gw_eq z u]
  have h1 : |u * (u ^ 2 + z.re ^ 2 - z.im ^ 2) /
      ((u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2)| =
      u * |u ^ 2 + z.re ^ 2 - z.im ^ 2| /
        ((u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2) := by
    rw [abs_div, abs_mul, abs_of_nonneg hu, abs_of_pos hD]
  rw [h1]
  have hstep : u * |u ^ 2 + z.re ^ 2 - z.im ^ 2| /
      ((u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2) ≤
      u / (2 * Real.sqrt (4 * z.re ^ 2 * z.im ^ 2)) := by
    rw [div_le_div_iff₀ hD (by positivity)]
    nlinarith [hAM, hu, abs_nonneg (u ^ 2 + z.re ^ 2 - z.im ^ 2)]
  have hfin : u / (2 * Real.sqrt (4 * z.re ^ 2 * z.im ^ 2)) ≤ 4 * u := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsqrt, hu]
  linarith

/-- Small-`u` bound on the logarithmic derivative factor. -/
private lemma Pw_abs_le_small {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 8) :
    |(-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
      (1 - Real.exp (-2 * Real.pi * u)))| ≤ 2 / u := by
  have hA := one_sub_exp_ge hu0 hu
  have hApos : 0 < 1 - Real.exp (-2 * Real.pi * u) := by
    have h : 0 < Real.pi * u := by positivity
    linarith
  have hEpos : 0 < Real.exp (-2 * Real.pi * u) := Real.exp_pos _
  have hEle : Real.exp (-2 * Real.pi * u) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos]
  have h1 : |(-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
      (1 - Real.exp (-2 * Real.pi * u)))| =
      2 * Real.pi * Real.exp (-2 * Real.pi * u) / (1 - Real.exp (-2 * Real.pi * u)) := by
    rw [abs_div, abs_of_pos hApos,
      show |-2 * Real.pi * Real.exp (-2 * Real.pi * u)| =
        2 * Real.pi * Real.exp (-2 * Real.pi * u) by
        rw [show -2 * Real.pi * Real.exp (-2 * Real.pi * u) =
          -(2 * Real.pi * Real.exp (-2 * Real.pi * u)) by ring, abs_neg,
          abs_of_pos (by positivity)]]
  rw [h1, div_le_div_iff₀ hApos hu0]
  have hmul : 2 * Real.exp (-2 * Real.pi * u) * (Real.pi * u) ≤
      2 * Real.exp (-2 * Real.pi * u) * (1 - Real.exp (-2 * Real.pi * u)) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have hmul2 : 2 * Real.exp (-2 * Real.pi * u) * (1 - Real.exp (-2 * Real.pi * u)) ≤
      2 * (1 - Real.exp (-2 * Real.pi * u)) := by nlinarith [hEle, hApos]
  nlinarith [hmul, hmul2]

/-- Large-`u` bound on the logarithmic derivative factor. -/
private lemma Pw_abs_le_exp {u : ℝ} (hu : 1 / 8 ≤ u) :
    |(-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
      (1 - Real.exp (-2 * Real.pi * u)))|
      ≤ 4 * Real.pi * Real.exp (-2 * Real.pi * u) := by
  have hA := one_sub_exp_ge_half hu
  have hApos : 0 < 1 - Real.exp (-2 * Real.pi * u) := by linarith
  have hEpos : 0 < Real.exp (-2 * Real.pi * u) := Real.exp_pos _
  have h1 : |(-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
      (1 - Real.exp (-2 * Real.pi * u)))| =
      2 * Real.pi * Real.exp (-2 * Real.pi * u) / (1 - Real.exp (-2 * Real.pi * u)) := by
    rw [abs_div, abs_of_pos hApos,
      show |-2 * Real.pi * Real.exp (-2 * Real.pi * u)| =
        2 * Real.pi * Real.exp (-2 * Real.pi * u) by
        rw [show -2 * Real.pi * Real.exp (-2 * Real.pi * u) =
          -(2 * Real.pi * Real.exp (-2 * Real.pi * u)) by ring, abs_neg,
          abs_of_pos (by positivity)]]
  rw [h1, div_le_iff₀ hApos]
  have hmul : 4 * Real.pi * Real.exp (-2 * Real.pi * u) * (1 / 2) ≤
      4 * Real.pi * Real.exp (-2 * Real.pi * u) * (1 - Real.exp (-2 * Real.pi * u)) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  nlinarith [hmul, hEpos, Real.pi_pos]

/-- `1 - exp (-2 pi x)` is positive for positive `x`. -/
private lemma one_sub_exp_pos {x : ℝ} (hx : 0 < x) :
    0 < 1 - Real.exp (-2 * Real.pi * x) := by
  have h : Real.exp (-2 * Real.pi * x) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  linarith

/-- `u * exp (-2 pi u) ≤ exp (-pi u)` on the positive half line. -/
private lemma mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) :
    u * Real.exp (-2 * Real.pi * u) ≤ Real.exp (-Real.pi * u) := by
  have h1 : u ≤ Real.exp (Real.pi * u) := by
    have h := Real.add_one_le_exp (Real.pi * u)
    have h2 : u ≤ 1 + Real.pi * u := by nlinarith [Real.pi_gt_three, hu]
    linarith
  have h2 : Real.exp (Real.pi * u) * Real.exp (-2 * Real.pi * u) = Real.exp (-Real.pi * u) := by
    rw [← Real.exp_add, show Real.pi * u + -2 * Real.pi * u = -Real.pi * u by ring]
  calc u * Real.exp (-2 * Real.pi * u) ≤
        Real.exp (Real.pi * u) * Real.exp (-2 * Real.pi * u) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-Real.pi * u) := h2

/-- The Binet kernel is the logarithmic derivative times the derivative of the
antiderivative, up to `1/pi`. -/
private lemma binetKernel_parts (z : ℂ) (hz1 : z.re ≠ 0) (hz2 : z.im ≠ 0) {u : ℝ}
    (hu : 0 < u) :
    binetKernel z u = (1 / Real.pi) *
      (((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
        (-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
          (1 - Real.exp (-2 * Real.pi * u)))) := by
  have hApos := one_sub_exp_pos hu
  have hEpos : (0 : ℝ) < Real.exp (-2 * Real.pi * u) := Real.exp_pos _
  have ha2 : 0 < z.re ^ 2 := sq_pos_of_ne_zero hz1
  have hb2 : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz2
  have hm2 : 0 < 4 * z.re ^ 2 * z.im ^ 2 := by positivity
  have hD : 0 < (u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
    nlinarith [sq_nonneg (u ^ 2 + z.re ^ 2 - z.im ^ 2)]
  have hXX : Real.exp (2 * Real.pi * u) = (Real.exp (-2 * Real.pi * u))⁻¹ := by
    rw [exp_neg_two_pi u, inv_inv]
  have hbig : (1 : ℝ) < Real.exp (2 * Real.pi * u) := by
    have h := Real.add_one_le_exp (2 * Real.pi * u)
    nlinarith [Real.pi_pos]
  have hXne : (Real.exp (-2 * Real.pi * u))⁻¹ - 1 ≠ 0 := by
    rw [← hXX]
    linarith
  rw [Gw_eq z u]
  unfold binetKernel
  rw [hXX]
  field_simp
  try ring

/-- The antiderivative `u / (u^2 + z^2)` has real part with the stated derivative. -/
private lemma deriv_Gw (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re)
      (((z ^ 2 - (x : ℂ) ^ 2) / ((x : ℂ) ^ 2 + z ^ 2) ^ 2)).re x := by
  have hxne : ((x : ℂ) ^ 2 + z ^ 2) ≠ 0 := by
    intro h
    have h0 : ‖(x : ℂ) ^ 2 + z ^ 2‖ ^ 2 = 0 := by rw [h]; simp
    have hlo := D_lower_u z hz x
    nlinarith [h0, hlo, hx]
  have hlin : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 x := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x := x) (hasDerivAt_id x)
    convert h using 1
    · funext y
      rfl
    · exact (Complex.ofRealCLM_apply _).symm
  have hsq : HasDerivAt (fun u : ℝ => (u : ℂ) ^ 2) (2 * (x : ℂ)) x := by
    have h := hlin.pow 2
    convert h using 1
    push_cast
    ring
  have hsum : HasDerivAt (fun u : ℝ => (u : ℂ) ^ 2 + z ^ 2) (2 * (x : ℂ)) x :=
    hsq.add_const _
  have hdiv := hlin.div hsum hxne
  have hval : (1 * ((x : ℂ) ^ 2 + z ^ 2) - (x : ℂ) * (2 * (x : ℂ))) /
      (((x : ℂ) ^ 2 + z ^ 2) ^ 2) = (z ^ 2 - (x : ℂ) ^ 2) / (((x : ℂ) ^ 2 + z ^ 2) ^ 2) := by
    ring
  rw [hval] at hdiv
  have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (x := x) hdiv
  convert hcomp using 1
  · funext y
    rfl
  · rfl

/-- The logarithmic kernel has the stated derivative. -/
private lemma deriv_logKernel {x : ℝ} (hx : 0 < x) :
    HasDerivAt LogKernel429.logKernel
      (-2 * Real.pi * Real.exp (-2 * Real.pi * x) /
        (1 - Real.exp (-2 * Real.pi * x))) x := by
  have hApos := one_sub_exp_pos hx
  have hE : HasDerivAt (fun u : ℝ => Real.exp (-2 * Real.pi * u))
      (Real.exp (-2 * Real.pi * x) * (-2 * Real.pi)) x := by
    have h1 : HasDerivAt (fun u : ℝ => -2 * Real.pi * u) (-2 * Real.pi) x := by
      simpa using (hasDerivAt_id x).const_mul (-2 * Real.pi)
    exact h1.exp
  have hA : HasDerivAt (fun u : ℝ => 1 - Real.exp (-2 * Real.pi * u))
      (2 * Real.pi * Real.exp (-2 * Real.pi * x)) x := by
    have h := hE.const_sub 1
    convert h using 1
    ring
  have hinv : HasDerivAt (fun u : ℝ => (1 - Real.exp (-2 * Real.pi * u))⁻¹)
      (-(2 * Real.pi * Real.exp (-2 * Real.pi * x)) /
        (1 - Real.exp (-2 * Real.pi * x)) ^ 2) x := hA.inv hApos.ne'
  have hlog := hinv.log (inv_ne_zero hApos.ne')
  have hfun : LogKernel429.logKernel =
      fun u : ℝ => Real.log ((1 - Real.exp (-2 * Real.pi * u))⁻¹) := by
    funext u
    rw [LogKernel429.logKernel, one_div]
  rw [hfun]
  exact hlog.congr_deriv (pw_deriv_eq (Real.exp (-2 * Real.pi * x)) (by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]))

/-- `Gw * Pw` is integrable on the positive half line. -/
private lemma integrable_GwPw (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hxy : z.re ^ 2 < z.im ^ 2) :
    IntegrableOn (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
      (-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
        (1 - Real.exp (-2 * Real.pi * u)))) (Set.Ioi 0) := by
  have hm : Measurable (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
      (-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
        (1 - Real.exp (-2 * Real.pi * u)))) := by
    fun_prop
  have h1 : IntegrableOn (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
      (-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
        (1 - Real.exp (-2 * Real.pi * u)))) (Set.Ioc 0 (1 / 8)) := by
    have hexpint : IntegrableOn (fun u : ℝ => Real.exp (-(Real.pi * u))) (Set.Ioi 0) := by
      have h := integrableOn_exp_mul_Ioi (a := -Real.pi) (by linarith [Real.pi_pos]) (0 : ℝ)
      have heq : (fun u : ℝ => Real.exp (-(Real.pi * u))) =
          (fun u : ℝ => Real.exp ((-Real.pi) * u)) := by
        funext u
        rw [neg_mul]
      rwa [heq]
    have hg : IntegrableOn (fun u : ℝ => (8 * Real.exp (Real.pi / 8)) * Real.exp (-(Real.pi * u)))
        (Set.Ioc 0 (1 / 8)) := by
      have h0 : IntegrableOn (fun u : ℝ => (8 * Real.exp (Real.pi / 8)) * Real.exp (-(Real.pi * u)))
          (Set.Ioi 0) := hexpint.const_mul (8 * Real.exp (Real.pi / 8))
      exact h0.mono_set (by intro u hu; exact hu.1)
    refine hg.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_mul]
    have hb1 := Gw_abs_le_lin z hz hxy hu.1.le
    have hb2 := Pw_abs_le_small hu.1 hu.2
    have hprod : |((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re| *
        |(-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
          (1 - Real.exp (-2 * Real.pi * u)))| ≤ 8 := by
      have hstep : |((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re| *
          |(-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
            (1 - Real.exp (-2 * Real.pi * u)))| ≤ 4 * u * (2 / u) :=
        mul_le_mul hb1 hb2 (abs_nonneg _) (by linarith [hu.1] : (0:ℝ) ≤ 4 * u)
      have hval : 4 * u * (2 / u) = 8 := by
        have hu0 : u ≠ 0 := ne_of_gt hu.1
        field_simp
        ring
      linarith
    have hexpge : (1 : ℝ) ≤ Real.exp (Real.pi / 8) * Real.exp (-(Real.pi * u)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have h1 : (0:ℝ) ≤ Real.pi * (1 / 8 - u) :=
        mul_nonneg Real.pi_pos.le (by linarith [hu.2])
      nlinarith
    nlinarith [hprod, hexpge]
  have h2 : IntegrableOn (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
      (-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
        (1 - Real.exp (-2 * Real.pi * u)))) (Set.Ioi (1 / 8)) := by
    have hexpint : IntegrableOn (fun u : ℝ => Real.exp (-(Real.pi * u))) (Set.Ioi (1 / 8)) := by
      have h := integrableOn_exp_mul_Ioi (a := -Real.pi) (by linarith [Real.pi_pos]) (1 / 8)
      have heq : (fun u : ℝ => Real.exp (-(Real.pi * u))) =
          (fun u : ℝ => Real.exp ((-Real.pi) * u)) := by
        funext u
        rw [neg_mul]
      rwa [heq]
    have hg : IntegrableOn (fun u : ℝ => (16 * Real.pi) * Real.exp (-(Real.pi * u)))
        (Set.Ioi (1 / 8)) := hexpint.const_mul (16 * Real.pi)
    refine hg.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul]
    have hu' : (1 / 8 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := by linarith
    have hb1 := Gw_abs_le_lin z hz hxy hu0.le
    have hb2 := Pw_abs_le_exp hu.le
    have hmul := mul_exp_neg_le hu0.le
    have hstep : |((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re| *
        |(-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
          (1 - Real.exp (-2 * Real.pi * u)))| ≤
        16 * Real.pi * (u * Real.exp (-2 * Real.pi * u)) := by
      have hle := mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)
      nlinarith [hle]
    have hbr : Real.exp (-Real.pi * u) = Real.exp (-(Real.pi * u)) := by
      congr 1
      ring
    rw [hbr] at hmul
    nlinarith [hstep, hmul, Real.pi_pos]
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 8)]
  exact h1.union h2

/-- The derivative product is integrable on the positive half line. -/
private lemma integrable_GwPhi (z : ℂ) (hker : IntegrableOn (partsKernel z) (Set.Ioi 0)) :
    IntegrableOn (fun u : ℝ => (((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re *
      LogKernel429.logKernel u) (Set.Ioi 0) := by
  have hm : Measurable (fun u : ℝ => (((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re *
      LogKernel429.logKernel u) := by
    unfold LogKernel429.logKernel
    fun_prop
  refine hker.mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hφ := LogKernel429.log_kernel_nonneg u hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hφ]
  have hle := Gw'_le z u
  have hpk : partsKernel z u =
      ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 * LogKernel429.logKernel u := rfl
  rw [hpk]
  exact mul_le_mul_of_nonneg_right hle hφ

/-- `Gw * logKernel` vanishes at `0+`. -/
private lemma tendsto_GwPhi_zero (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hxy : z.re ^ 2 < z.im ^ 2) :
    Filter.Tendsto (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re * LogKernel429.logKernel u)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hlim : Filter.Tendsto (fun u : ℝ => 4 * (u * Real.log (1 / (Real.pi * u))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using tendsto_mul_log_inv.const_mul 4
  refine squeeze_zero_norm' ?_ hlim
  have hsmall : ∀ᶠ u : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), u ≤ 1 / 8 := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with u hu
    exact hu.2
  filter_upwards [self_mem_nhdsWithin, hsmall] with u hu hu8
  have hu0 : (0 : ℝ) < u := hu
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (LogKernel429.log_kernel_nonneg u hu)]
  have hb1 := Gw_abs_le_lin z hz hxy hu0.le
  have hb2 := logKernel_le_log_inv hu hu8
  calc |((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re| * LogKernel429.logKernel u
      ≤ 4 * u * Real.log (1 / (Real.pi * u)) :=
        mul_le_mul hb1 hb2 (LogKernel429.log_kernel_nonneg u hu)
          (by linarith [hu0] : (0:ℝ) ≤ 4 * u)
    _ = 4 * (u * Real.log (1 / (Real.pi * u))) := by ring

/-- `Gw * logKernel` vanishes at `+infinity`. -/
private lemma tendsto_GwPhi_atTop (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hxy : z.re ^ 2 < z.im ^ 2) :
    Filter.Tendsto (fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re * LogKernel429.logKernel u)
      Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun u : ℝ => 8 * Real.exp (-Real.pi * u)) Filter.atTop (nhds 0) := by
    simpa using tendsto_exp_neg_pi_atTop.const_mul 8
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun u hu => hu⟩] with u hu
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (LogKernel429.log_kernel_nonneg u (by linarith))]
  have hb1 := Gw_abs_le_lin z hz hxy (by linarith : (0 : ℝ) ≤ u)
  have hb2 := logKernel_le_two_exp (by linarith : (1 / 2 : ℝ) ≤ u)
  have hmul := mul_exp_neg_le (by linarith : (0 : ℝ) ≤ u)
  have hstep : |((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re| * LogKernel429.logKernel u ≤
      8 * (u * Real.exp (-2 * Real.pi * u)) := by
    have h0 : (0 : ℝ) < u * Real.exp (-2 * Real.pi * u) :=
      mul_pos (by linarith) (Real.exp_pos _)
    have hle := mul_le_mul hb1 hb2 (LogKernel429.log_kernel_nonneg u (by linarith))
      (by linarith : (0:ℝ) ≤ 4 * u)
    linarith [hle]
  have hmul' : u * Real.exp (-2 * Real.pi * u) ≤ Real.exp (-(Real.pi * u)) := by
    have hbr : Real.exp (-Real.pi * u) = Real.exp (-(Real.pi * u)) := by
      congr 1
      ring
    rw [hbr] at hmul
    exact hmul
  calc |((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re| * LogKernel429.logKernel u
      ≤ 8 * (u * Real.exp (-2 * Real.pi * u)) := hstep
    _ ≤ 8 * Real.exp (-Real.pi * u) := by nlinarith [hmul]


/-- LEAF. Chandee Appendix page 13, first display after display 24.
Integration by parts and the norm inequality split the Binet remainder
at norm z over three. Integrability of both resulting pieces is explicit.
No numerical bound for either piece occurs here. -/
theorem binet_split (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hn : 4 ≤ ‖z‖) (hxy : z.re ^ 2 < z.im ^ 2) :
    IntegrableOn (partsKernel z) (Set.Ioc 0 (‖z‖ / 3)) ∧
    IntegrableOn (partsKernel z) (Set.Ioi (‖z‖ / 3)) ∧
    binetRemainder z ≤
      (1 / Real.pi) * (∫ u in Set.Ioc 0 (‖z‖ / 3), partsKernel z u) +
      (1 / Real.pi) * (∫ u in Set.Ioi (‖z‖ / 3), partsKernel z u) := by
  refine ⟨parts_integrable_head z hz hn, parts_integrable_tail z hz hn, ?_⟩
  have hR0 : (0 : ℝ) < ‖z‖ := by linarith
  have hR3 : (0 : ℝ) < ‖z‖ / 3 := by linarith
  have hker : IntegrableOn (partsKernel z) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hR3.le]
    exact (parts_integrable_head z hz hn).union (parts_integrable_tail z hz hn)
  have hIBP :
      ∫ u in Set.Ioi (0 : ℝ), ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
        (-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
          (1 - Real.exp (-2 * Real.pi * u)))
      = 0 - 0 - ∫ u in Set.Ioi (0 : ℝ),
          (((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re *
            LogKernel429.logKernel u := by
    exact integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ))
      (u := fun u : ℝ => ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re)
      (v := LogKernel429.logKernel)
      (u' := fun u : ℝ => (((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re)
      (v' := fun u : ℝ => -2 * Real.pi * Real.exp (-2 * Real.pi * u) /
          (1 - Real.exp (-2 * Real.pi * u)))
      (fun x hx => deriv_Gw z hz hx)
      (fun x hx => deriv_logKernel hx)
      (integrable_GwPw z hz hxy)
      (integrable_GwPhi z hker)
      (tendsto_GwPhi_zero z hz hxy)
      (tendsto_GwPhi_atTop z hz hxy)
  have hrem : binetRemainder z = (1 / Real.pi) *
      ∫ u in Set.Ioi (0 : ℝ), ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
        (-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
          (1 - Real.exp (-2 * Real.pi * u))) := by
    unfold binetRemainder
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    refine binetKernel_parts z ?_ ?_ hu
    · intro h
      rw [h] at hz
      norm_num at hz
    · intro h
      rw [h, pow_two] at hxy
      nlinarith [sq_nonneg z.re]
  have hneg : ∫ u in Set.Ioi (0 : ℝ), ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
        (-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
          (1 - Real.exp (-2 * Real.pi * u)))
      = -∫ u in Set.Ioi (0 : ℝ),
          (((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re *
            LogKernel429.logKernel u := by
    rw [hIBP]
    ring
  have hI1 : -(∫ u in Set.Ioi (0 : ℝ), partsKernel z u) ≤
      ∫ u in Set.Ioi (0 : ℝ),
        (((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re *
          LogKernel429.logKernel u := by
    have hGi := integrable_GwPhi z hker
    have h3 : -(∫ u in Set.Ioi (0 : ℝ),
            ‖(((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re *
              LogKernel429.logKernel u‖) ≤
        ∫ u in Set.Ioi (0 : ℝ),
          (((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re *
            LogKernel429.logKernel u :=
      (by
        simpa [integral_neg, Real.norm_eq_abs, abs_mul] using
          setIntegral_mono_on hGi.abs.neg hGi measurableSet_Ioi
            (fun u _ => neg_abs_le _))
    have h2 : ∫ u in Set.Ioi (0 : ℝ),
          ‖(((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re *
            LogKernel429.logKernel u‖
        ≤ ∫ u in Set.Ioi (0 : ℝ), partsKernel z u := by
      refine setIntegral_mono_on hGi.abs hker measurableSet_Ioi ?_
      intro u hu
      have hφ := LogKernel429.log_kernel_nonneg u hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hφ]
      have hle := Gw'_le z u
      have hpk : partsKernel z u =
          ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 *
            LogKernel429.logKernel u := rfl
      rw [hpk]
      exact mul_le_mul_of_nonneg_right hle hφ
    linarith
  have hsplit : ∫ u in Set.Ioi (0 : ℝ), partsKernel z u =
      (∫ u in Set.Ioc (0 : ℝ) (‖z‖ / 3), partsKernel z u) +
      (∫ u in Set.Ioi (‖z‖ / 3), partsKernel z u) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hR3.le]
    exact setIntegral_union
      (by rw [Set.disjoint_left]; intro u hu1 hu2; exact absurd hu1.2 (not_le.mpr hu2))
      measurableSet_Ioi (parts_integrable_head z hz hn) (parts_integrable_tail z hz hn)
  calc binetRemainder z
      = (1 / Real.pi) * ∫ u in Set.Ioi (0 : ℝ), ((u : ℂ) / ((u : ℂ) ^ 2 + z ^ 2)).re *
          (-2 * Real.pi * Real.exp (-2 * Real.pi * u) /
            (1 - Real.exp (-2 * Real.pi * u))) := hrem
    _ = (1 / Real.pi) * -∫ u in Set.Ioi (0 : ℝ),
          (((z ^ 2 - (u : ℂ) ^ 2) / ((u : ℂ) ^ 2 + z ^ 2) ^ 2)).re *
            LogKernel429.logKernel u := by rw [hneg]
    _ ≤ (1 / Real.pi) * ∫ u in Set.Ioi (0 : ℝ), partsKernel z u := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = (1 / Real.pi) * (∫ u in Set.Ioc (0 : ℝ) (‖z‖ / 3), partsKernel z u) +
        (1 / Real.pi) * (∫ u in Set.Ioi (‖z‖ / 3), partsKernel z u) := by
      rw [hsplit]
      ring


/-- LEAF. Chandee Appendix page 13, first integral estimate after display 24.
The local norm ratio is at most 45 divided by 32 norm z squared. The
logarithmic kernel integral supplies the factor pi over twelve. -/
theorem parts_head (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hn : 4 ≤ ‖z‖) (hxy : z.re ^ 2 < z.im ^ 2) :
    (1 / Real.pi) * (∫ u in Set.Ioc 0 (‖z‖ / 3), partsKernel z u) ≤
      15 / (128 * ‖z‖ ^ 2) := by
  let C : ℝ := 45 / (32 * ‖z‖ ^ 2)
  have hz0 : z ≠ 0 := by
    intro he
    norm_num [he] at hn
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsub : Set.Ioc (0 : ℝ) (‖z‖ / 3) ⊆ Set.Ioi 0 := by
    intro u hu
    exact hu.1
  have hg := LogKernel429.log_kernel_integrable.mono_set hsub
  have hi := hg.const_mul C
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioc (0 : ℝ) (‖z‖ / 3)) :
      partsKernel z u ≤ C * LogKernel429.logKernel u := by
    have hh := mul_le_mul_of_nonneg_right
      (GammaGeometry429.head_norm_ratio z hz0 u hu.1.le hu.2)
      (LogKernel429.log_kernel_nonneg u hu.1)
    simpa only [partsKernel, LogKernel429.logKernel, C] using hh
  have hnonneg (u : ℝ) (hu : 0 < u) : 0 ≤ partsKernel z u := by
    have hh := LogKernel429.log_kernel_nonneg u hu
    change 0 ≤ _ * LogKernel429.logKernel u
    positivity
  have hm : Measurable (partsKernel z) := by
    unfold partsKernel
    fun_prop
  have hp : IntegrableOn (partsKernel z) (Set.Ioc (0 : ℝ) (‖z‖ / 3)) := by
    apply hi.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u hu.1)]
    exact hpoint u hu
  have hhead : (∫ u in Set.Ioc (0 : ℝ) (‖z‖ / 3), partsKernel z u) ≤
      C * (∫ u in Set.Ioc (0 : ℝ) (‖z‖ / 3), LogKernel429.logKernel u) := by
    calc
      _ ≤ ∫ u in Set.Ioc (0 : ℝ) (‖z‖ / 3), C * LogKernel429.logKernel u :=
        setIntegral_mono_on hp hi measurableSet_Ioc hpoint
      _ = _ := integral_const_mul C _
  have hlog : (∫ u in Set.Ioc (0 : ℝ) (‖z‖ / 3), LogKernel429.logKernel u) ≤ Real.pi / 12 := by
    rw [← LogKernel429.log_kernel_integral]
    apply setIntegral_mono_set LogKernel429.log_kernel_integrable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact LogKernel429.log_kernel_nonneg u hu
    · exact Filter.Eventually.of_forall hsub
  calc
    _ ≤ (1 / Real.pi) * (C * (Real.pi / 12)) :=
      mul_le_mul_of_nonneg_left
        (hhead.trans (mul_le_mul_of_nonneg_left hlog hC)) (by positivity)
    _ = _ := by
      dsimp [C]
      have hn0 : ‖z‖ ≠ 0 := by linarith
      field_simp [Real.pi_ne_zero, hn0]
      ring

/-- LEAF. Chandee Appendix page 13, second integral estimate after display 24.
The denominator factorization and the exponential logarithm tail bound
control only the unbounded piece. -/
theorem parts_tail (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hn : 4 ≤ ‖z‖) (hxy : z.re ^ 2 < z.im ^ 2) :
    (1 / Real.pi) * (∫ u in Set.Ioi (‖z‖ / 3), partsKernel z u) ≤
      4 * Real.exp (-2 * Real.pi * ‖z‖ / 3) / 3 * (1 + 1 / ‖z‖ ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hR0 : (0 : ℝ) < ‖z‖ := by linarith
  have hR2 : (16 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
  have hR3 : (0 : ℝ) < ‖z‖ / 3 := by linarith
  have hR2p : (0 : ℝ) < ‖z‖ / 2 := by linarith
  have hle : ‖z‖ / 3 ≤ ‖z‖ / 2 := by linarith
  have hm : Measurable (partsKernel z) := by
    unfold partsKernel
    fun_prop
  have hnonneg : ∀ u : ℝ, 0 < u → 0 ≤ partsKernel z u := by
    intro u hu
    have hh := LogKernel429.log_kernel_nonneg u hu
    change 0 ≤ _ * LogKernel429.logKernel u
    positivity
  -- pointwise bounds on the two pieces
  have hb1 : ∀ u ∈ Set.Ioc (‖z‖ / 3) (‖z‖ / 2),
      partsKernel z u ≤ (5 / (2 * ‖z‖ ^ 2)) * LogKernel429.logKernel u := by
    intro u hu
    have hu0 : 0 < u := lt_trans hR3 hu.1
    have hratio := ratio_head_le z hu0 hu.2
    have hφ := LogKernel429.log_kernel_nonneg u hu0
    have hfe : partsKernel z u =
        ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 * LogKernel429.logKernel u := rfl
    rw [hfe]
    exact mul_le_mul_of_nonneg_right hratio hφ
  have hb2 : ∀ u ∈ Set.Ioi (‖z‖ / 2),
      partsKernel z u ≤ 20 * LogKernel429.logKernel u := by
    intro u hu
    have hu0 : 0 < u := lt_trans hR2p hu
    have hratio := ratio_tail_le z hz hu.le
    have hφ := LogKernel429.log_kernel_nonneg u hu0
    have hfe : partsKernel z u =
        ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 * LogKernel429.logKernel u := rfl
    rw [hfe]
    exact mul_le_mul_of_nonneg_right hratio hφ
  -- dominating integrands
  have hdom1 : IntegrableOn (fun u : ℝ => (5 / (2 * ‖z‖ ^ 2)) * LogKernel429.logKernel u)
      (Set.Ioc (‖z‖ / 3) (‖z‖ / 2)) :=
    (LogKernel429.log_kernel_integrable.mono_set
      (by intro u hu; exact lt_trans hR3 hu.1)).const_mul _
  have hdom2 : IntegrableOn (fun u : ℝ => 20 * LogKernel429.logKernel u)
      (Set.Ioi (‖z‖ / 2)) :=
    (LogKernel429.log_kernel_integrable.mono_set (Set.Ioi_subset_Ioi hR2p.le)).const_mul _
  have hp1 : IntegrableOn (partsKernel z) (Set.Ioc (‖z‖ / 3) (‖z‖ / 2)) := by
    refine hdom1.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u (lt_trans hR3 hu.1))]
    exact hb1 u hu
  have hp2 : IntegrableOn (partsKernel z) (Set.Ioi (‖z‖ / 2)) := by
    refine hdom2.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u (lt_trans hR2p hu))]
    exact hb2 u hu
  -- integral bounds on the two pieces
  have hI1 : (∫ u in Set.Ioc (‖z‖ / 3) (‖z‖ / 2), partsKernel z u) ≤
      (5 / (2 * ‖z‖ ^ 2)) * (∫ u in Set.Ioc (‖z‖ / 3) (‖z‖ / 2),
        LogKernel429.logKernel u) := by
    calc (∫ u in Set.Ioc (‖z‖ / 3) (‖z‖ / 2), partsKernel z u)
        ≤ ∫ u in Set.Ioc (‖z‖ / 3) (‖z‖ / 2),
            (5 / (2 * ‖z‖ ^ 2)) * LogKernel429.logKernel u :=
          setIntegral_mono_on hp1 hdom1 measurableSet_Ioc hb1
      _ = _ := integral_const_mul _ _
  have hI2 : (∫ u in Set.Ioi (‖z‖ / 2), partsKernel z u) ≤
      20 * (∫ u in Set.Ioi (‖z‖ / 2), LogKernel429.logKernel u) := by
    calc (∫ u in Set.Ioi (‖z‖ / 2), partsKernel z u)
        ≤ ∫ u in Set.Ioi (‖z‖ / 2), 20 * LogKernel429.logKernel u :=
          setIntegral_mono_on hp2 hdom2 measurableSet_Ioi hb2
      _ = _ := integral_const_mul _ _
  -- logarithm tail bounds
  have hL1 : (∫ u in Set.Ioc (‖z‖ / 3) (‖z‖ / 2), LogKernel429.logKernel u) ≤
      Real.exp (-2 * Real.pi * ‖z‖ / 3) / Real.pi := by
    have htail := tail_phi_integral (c := ‖z‖ / 3) (by linarith)
    have harg : -2 * Real.pi * (‖z‖ / 3) = -2 * Real.pi * ‖z‖ / 3 := by ring
    rw [harg] at htail
    refine le_trans ?_ htail
    apply setIntegral_mono_set (LogKernel429.log_kernel_integrable.mono_set
      (by intro u hu; exact lt_trans hR3 hu))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact LogKernel429.log_kernel_nonneg u (lt_trans hR3 hu)
    · exact Filter.Eventually.of_forall (by
        intro u hu
        exact hu.1)
  have hL2 : (∫ u in Set.Ioi (‖z‖ / 2), LogKernel429.logKernel u) ≤
      Real.exp (-Real.pi * ‖z‖) / Real.pi := by
    have htail := tail_phi_integral (c := ‖z‖ / 2) (by linarith)
    have harg : -2 * Real.pi * (‖z‖ / 2) = -Real.pi * ‖z‖ := by ring
    rw [harg] at htail
    exact htail
  -- split the integral
  have hsplit : (∫ u in Set.Ioi (‖z‖ / 3), partsKernel z u) =
      (∫ u in Set.Ioc (‖z‖ / 3) (‖z‖ / 2), partsKernel z u) +
      (∫ u in Set.Ioi (‖z‖ / 2), partsKernel z u) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hle]
    exact setIntegral_union
      (by rw [Set.disjoint_left]; intro u hu1 hu2; exact absurd hu1.2 (not_le.mpr hu2))
      measurableSet_Ioi hp1 hp2
  -- exponential comparison
  have hexp8 : Real.exp (-Real.pi * ‖z‖) ≤
      (1 / 8) * Real.exp (-2 * Real.pi * ‖z‖ / 3) := by
    have hlog8 : Real.log 8 ≤ 3 := log_eight_le_three
    have harg : -Real.pi * ‖z‖ ≤ -2 * Real.pi * ‖z‖ / 3 + -3 := by
      nlinarith
    calc Real.exp (-Real.pi * ‖z‖) ≤ Real.exp (-2 * Real.pi * ‖z‖ / 3 + -3) :=
          Real.exp_le_exp.mpr harg
      _ = Real.exp (-2 * Real.pi * ‖z‖ / 3) * Real.exp (-3) := Real.exp_add _ _
      _ ≤ Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 / 8) := by
          have h8 : Real.exp (-3 : ℝ) ≤ (1 / 8 : ℝ) := by
            rw [Real.exp_neg]
            simpa only [one_div] using
              one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8) exp_three_ge_eight
          exact mul_le_mul_of_nonneg_left h8 (Real.exp_pos _).le
      _ = (1 / 8) * Real.exp (-2 * Real.pi * ‖z‖ / 3) := by ring
  -- assemble
  have hA : (∫ u in Set.Ioc (‖z‖ / 3) (‖z‖ / 2), partsKernel z u) ≤
      (5 / (2 * ‖z‖ ^ 2)) * (Real.exp (-2 * Real.pi * ‖z‖ / 3) / Real.pi) :=
    le_trans hI1 (mul_le_mul_of_nonneg_left hL1 (by positivity))
  have hB20 : 20 * (Real.exp (-Real.pi * ‖z‖) / Real.pi) ≤
      (5 / 2) * (Real.exp (-2 * Real.pi * ‖z‖ / 3) / Real.pi) := by
    have h := mul_le_mul_of_nonneg_right hexp8 (by positivity : (0:ℝ) ≤ 1 / Real.pi)
    have he : Real.exp (-Real.pi * ‖z‖) / Real.pi =
        Real.exp (-Real.pi * ‖z‖) * (1 / Real.pi) := by ring
    have he2 : Real.exp (-2 * Real.pi * ‖z‖ / 3) / Real.pi =
        Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 / Real.pi) := by ring
    rw [he, he2]
    nlinarith
  have hB : (∫ u in Set.Ioi (‖z‖ / 2), partsKernel z u) ≤
      (5 / 2) * (Real.exp (-2 * Real.pi * ‖z‖ / 3) / Real.pi) :=
    le_trans hI2 (le_trans (mul_le_mul_of_nonneg_left hL2 (by norm_num)) hB20)
  have hX : (∫ u in Set.Ioi (‖z‖ / 3), partsKernel z u) ≤
      (Real.exp (-2 * Real.pi * ‖z‖ / 3) / Real.pi) * (5 / (2 * ‖z‖ ^ 2) + 5 / 2) := by
    rw [hsplit]
    calc (∫ u in Set.Ioc (‖z‖ / 3) (‖z‖ / 2), partsKernel z u) +
          (∫ u in Set.Ioi (‖z‖ / 2), partsKernel z u)
        ≤ (5 / (2 * ‖z‖ ^ 2)) * (Real.exp (-2 * Real.pi * ‖z‖ / 3) / Real.pi) +
          (5 / 2) * (Real.exp (-2 * Real.pi * ‖z‖ / 3) / Real.pi) := add_le_add hA hB
      _ = _ := by ring
  have hstep1 : (1 / Real.pi) * (∫ u in Set.Ioi (‖z‖ / 3), partsKernel z u) ≤
      (1 / Real.pi) *
        ((Real.exp (-2 * Real.pi * ‖z‖ / 3) / Real.pi) * (5 / (2 * ‖z‖ ^ 2) + 5 / 2)) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have hbsum : (5 : ℝ) / (2 * ‖z‖ ^ 2) + 5 / 2 ≤ 85 / 32 := by
    have h5 : (5 : ℝ) / (2 * ‖z‖ ^ 2) ≤ 5 / 32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hbsum0 : (0 : ℝ) ≤ 5 / (2 * ‖z‖ ^ 2) + 5 / 2 := by positivity
  have hpinv : (1 : ℝ) / Real.pi ^ 2 ≤ 1 / 9 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hEpos : (0 : ℝ) < Real.exp (-2 * Real.pi * ‖z‖ / 3) := Real.exp_pos _
  have hstep2 : (1 / Real.pi) *
      ((Real.exp (-2 * Real.pi * ‖z‖ / 3) / Real.pi) * (5 / (2 * ‖z‖ ^ 2) + 5 / 2)) ≤
      (4 / 3) * Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 + 1 / ‖z‖ ^ 2) := by
    have hfac : (1 / Real.pi) *
        ((Real.exp (-2 * Real.pi * ‖z‖ / 3) / Real.pi) * (5 / (2 * ‖z‖ ^ 2) + 5 / 2)) =
        (Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 / Real.pi ^ 2)) *
          (5 / (2 * ‖z‖ ^ 2) + 5 / 2) := by
      field_simp
    rw [hfac]
    have hle1 : Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 / Real.pi ^ 2) ≤
        Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 / 9) :=
      mul_le_mul_of_nonneg_left hpinv hEpos.le
    have hle2 : Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 / 9) * (5 / (2 * ‖z‖ ^ 2) + 5 / 2) ≤
        Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 / 9) * (85 / 32) := by
      apply mul_le_mul_of_nonneg_left hbsum
      positivity
    have hle3 : Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 / 9) * (85 / 32) ≤
        (4 / 3) * Real.exp (-2 * Real.pi * ‖z‖ / 3) := by
      nlinarith [hEpos]
    have hle4 : (4 / 3) * Real.exp (-2 * Real.pi * ‖z‖ / 3) ≤
        (4 / 3) * Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 + 1 / ‖z‖ ^ 2) := by
      have hge : (1 : ℝ) ≤ 1 + 1 / ‖z‖ ^ 2 := by
        have hp : (0 : ℝ) < 1 / ‖z‖ ^ 2 := by positivity
        linarith
      nlinarith [hEpos, hge]
    calc Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 / Real.pi ^ 2) * (5 / (2 * ‖z‖ ^ 2) + 5 / 2)
        ≤ Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 / 9) * (5 / (2 * ‖z‖ ^ 2) + 5 / 2) := by
          nlinarith [hle1, hbsum0]
      _ ≤ Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 / 9) * (85 / 32) := hle2
      _ ≤ (4 / 3) * Real.exp (-2 * Real.pi * ‖z‖ / 3) := hle3
      _ ≤ (4 / 3) * Real.exp (-2 * Real.pi * ‖z‖ / 3) * (1 + 1 / ‖z‖ ^ 2) := hle4
  linarith


/-- Chandee display 24, assembled from the three smaller integral leaves.
CONDITIONAL ON those leaves. -/
theorem binet_large_majorant (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hn : 4 ≤ ‖z‖) (hxy : z.re ^ 2 < z.im ^ 2) :
    binetRemainder z ≤ 15 / (128 * ‖z‖ ^ 2) +
      4 * Real.exp (-2 * Real.pi * ‖z‖ / 3) / 3 * (1 + 1 / ‖z‖ ^ 2) := by
  exact (binet_split z hz hn hxy).2.2 |>.trans
    (add_le_add (parts_head z hz hn hxy) (parts_tail z hz hn hxy))

/-- Chandee page 13, the reciprocal contribution before the final inequality. -/
theorem reciprocal_lower (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    1 / (8 * ‖z‖ ^ 2) ≤ (1 / (2 * z)).re := by
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (hz.trans (Complex.re_le_norm z))
  have hn : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  norm_num [Complex.div_re, Complex.normSq_mul, hn]
  have hn0 : ‖z‖ ^ 2 ≠ 0 := (sq_pos_of_pos hz0).ne'
  field_simp
  nlinarith [sq_pos_of_pos hz0]

/-- Exact existing Decomp377d.large_correction statement.
CONDITIONAL ON the smaller display 24 remainder estimate. -/
theorem large_correction (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hn : 4 ≤ ‖z‖) :
    -(1 / (2 * z)).re + binetRemainder z ≤ 0 := by
  by_cases hxy : z.im ^ 2 ≤ z.re ^ 2
  · exact correction_nonpos_of_im_sq_le z (by linarith) hxy
  · have h := (binet_large_majorant z hz hn (lt_of_not_ge hxy)).trans
      (exponential_absorption ‖z‖ hn)
    linarith [reciprocal_lower z hz]

end LeanLab.ChirreHagen2025.Decomp429a
