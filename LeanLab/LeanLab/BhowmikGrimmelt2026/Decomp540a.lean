/-
Auxiliary theta ray and exponential moment estimates for Hardy 1914.
Source: Comptes rendus 158, page 1012 display 1 and page 1013 displays 2 and 3.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BhowmikGrimmelt2026

open Real Complex Filter Topology MeasureTheory Set Asymptotics

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
noncomputable def expMomentIntegrand540 (f : ℝ → ℝ) (n : ℕ) (α t : ℝ) : ℝ :=
  (Real.exp (α * t) + (-1 : ℝ) ^ n * Real.exp (-α * t)) * t ^ n * f t

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
noncomputable def expMoment540 (f : ℝ → ℝ) (n : ℕ) (α : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, expMomentIntegrand540 f n α t

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem hasDerivAt_expMomentIntegrand540 (f : ℝ → ℝ) (n : ℕ) (α t : ℝ) :
    HasDerivAt (fun β => expMomentIntegrand540 f n β t)
      (expMomentIntegrand540 f (n + 1) α t) α := by
  have hp : HasDerivAt (fun β : ℝ => Real.exp (β * t)) (Real.exp (α * t) * t) α :=
    by simpa only [Function.comp_def, id_eq, one_mul] using (Real.hasDerivAt_exp _).comp α ((hasDerivAt_id α).mul_const t)
  have hn : HasDerivAt (fun β : ℝ => Real.exp (-β * t))
      (Real.exp (-α * t) * (-t)) α := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-α * t)).comp α (((hasDerivAt_id α).neg).mul_const t)
  have hh := ((hp.add (hn.const_mul ((-1 : ℝ) ^ n))).mul_const (t ^ n)).mul_const (f t)
  convert hh using 1
  · ext β
    simp only [expMomentIntegrand540, Pi.add_apply]
  · simp only [expMomentIntegrand540, pow_succ]
    ring

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem expMomentIntegrand_bound540 (f : ℝ → ℝ) (n : ℕ) (α t b φ C : ℝ)
    (ht : 0 ≤ t) (hα : |α| ≤ b) (_hC : 0 ≤ C)
    (hf : |f t| ≤ C * Real.exp (-φ * t)) :
    ‖expMomentIntegrand540 f n α t‖ ≤
      2 * C * (t ^ n * Real.exp (-(φ - b) * t)) := by
  have hpos : Real.exp (α * t) ≤ Real.exp (b * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((le_abs_self α).trans hα) ht)
  have hneg : Real.exp (-α * t) ≤ Real.exp (b * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((neg_le_abs α).trans hα) ht)
  have hweight : |Real.exp (α * t) + (-1 : ℝ) ^ n * Real.exp (-α * t)| ≤
      2 * Real.exp (b * t) := by
    calc
      _ ≤ |Real.exp (α * t)| + |(-1 : ℝ) ^ n * Real.exp (-α * t)| := abs_add_le _ _
      _ = Real.exp (α * t) + Real.exp (-α * t) := by simp
      _ ≤ _ := by linarith
  rw [expMomentIntegrand540, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg ht]
  calc
    _ ≤ (2 * Real.exp (b * t)) * t ^ n * (C * Real.exp (-φ * t)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hweight (pow_nonneg ht _)) hf
        (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [show -(φ - b) * t = b * t + -φ * t by ring, Real.exp_add]
      ring

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem integrable_expMoment_majorant540 (n : ℕ) (φ b C : ℝ) (hb : b < φ) :
    IntegrableOn (fun t : ℝ => 2 * C * (t ^ n * Real.exp (-(φ - b) * t))) (Ioi 0) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n : ℝ)) (p := 1) (b := φ - b) (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)) (by norm_num) (by linarith)
  simpa only [Real.rpow_natCast, Real.rpow_one, IntegrableOn] using hi.const_mul (2 * C)

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem continuous_expMomentIntegrand540 (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) (α : ℝ) :
    Continuous (expMomentIntegrand540 f n α) := by
  unfold expMomentIntegrand540
  fun_prop

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem integrable_expMoment540 (f : ℝ → ℝ) (hf : Continuous f) (φ C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ C * Real.exp (-φ * t))
    (n : ℕ) (α : ℝ) (hα : |α| < φ) :
    IntegrableOn (expMomentIntegrand540 f n α) (Ioi 0) := by
  refine (integrable_expMoment_majorant540 n φ |α| C hα).mono'
    (continuous_expMomentIntegrand540 f hf n α).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact expMomentIntegrand_bound540 f n α t |α| φ C ht.le le_rfl hC (hbound t ht.le)

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem hasDerivAt_expMoment540 (f : ℝ → ℝ) (hf : Continuous f) (φ C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ C * Real.exp (-φ * t))
    (n : ℕ) (α : ℝ) (hα : |α| < φ) :
    HasDerivAt (expMoment540 f n) (expMoment540 f (n + 1) α) α := by
  let b : ℝ := (|α| + φ) / 2
  have hab : |α| < b := by dsimp [b]; linarith
  have hbφ : b < φ := by dsimp [b]; linarith
  have hs : {β : ℝ | |β| < b} ∈ 𝓝 α :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hab
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := expMomentIntegrand540 f n)
    (F' := expMomentIntegrand540 f (n + 1)) hs
    (Eventually.of_forall fun β => (continuous_expMomentIntegrand540 f hf n β).aestronglyMeasurable)
    (integrable_expMoment540 f hf φ C hC hbound n α hα)
    (continuous_expMomentIntegrand540 f hf (n + 1) α).aestronglyMeasurable
    ?_ (integrable_expMoment_majorant540 (n + 1) φ b C hbφ) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro β hβ
    exact expMomentIntegrand_bound540 f (n + 1) β t b φ C ht.le hβ.le hC (hbound t ht.le)
  · exact Eventually.of_forall fun t β hβ => hasDerivAt_expMomentIntegrand540 f n β t

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem iteratedDeriv_expMoment540 (f : ℝ → ℝ) (hf : Continuous f) (φ C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ C * Real.exp (-φ * t))
    (n : ℕ) (α : ℝ) (hα : |α| < φ) :
    iteratedDeriv n (expMoment540 f 0) α = expMoment540 f n α := by
  induction n generalizing α with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (expMoment540 f 0) =ᶠ[𝓝 α] expMoment540 f n := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hα] with β hβ
      exact ih β hβ
    rw [he.deriv_eq]
    exact (hasDerivAt_expMoment540 f hf φ C hC hbound n α hα).deriv

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
noncomputable def thetaMellinKernel540 (z : ℂ) : ℂ :=
  z ^ 2 * iteratedDeriv 2 (fun w : ℂ => jacobiTheta (I * w)) z +
    (3 / 2 : ℂ) * z * deriv (fun w : ℂ => jacobiTheta (I * w)) z

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem differentiableOn_thetaMellinKernel540 :
    DifferentiableOn ℂ thetaMellinKernel540 {z : ℂ | 0 < z.re} := by
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hd : DifferentiableOn ℂ (fun w : ℂ => jacobiTheta (I * w)) {z : ℂ | 0 < z.re} := by
    intro z hz
    exact ((differentiableAt_jacobiTheta (by simpa using hz)).comp z
      (by fun_prop)).differentiableWithinAt
  have hdd := (hd.deriv ho).deriv ho
  intro z hz
  have hd1 := (hd.deriv ho).differentiableAt (ho.mem_nhds hz)
  have hd2 := hdd.differentiableAt (ho.mem_nhds hz)
  unfold thetaMellinKernel540
  have hh := ((differentiableAt_id.pow 2).mul hd2).add
    ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (3 / 2 : ℂ) * z) z).mul hd1)
  convert hh.differentiableWithinAt using 1
  ext w
  simp [iteratedDeriv_succ]

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem ray_positive_re540 (φ x : ℝ) (hφ : |φ| < Real.pi / 2) (hx : 0 < x) :
    0 < ((x : ℂ) * Complex.exp ((φ : ℂ) * I)).re := by
  simpa [Complex.exp_re] using mul_pos hx (Real.cos_pos_of_mem_Ioo (abs_lt.mp hφ))

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem continuousOn_theta_ray540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)))
      (Ioi 0) := by
  exact differentiableOn_thetaMellinKernel540.continuousOn.comp (by fun_prop)
    (fun x hx => ray_positive_re540 φ x hφ hx)

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem mellin_ray_phase_norm540 (φ t : ℝ) :
    ‖Complex.exp ((φ : ℂ) * I * ((1 / 4 : ℂ) + (t : ℂ) * I))‖ = Real.exp (-φ * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [mul_re, mul_im]

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem mellin_ray_power_norm540 (x t : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1)‖ = x ^ (-3 / 4 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1
  norm_num

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem theta_cauchy_bound540 (n : ℕ) (z : ℂ) (hz : 1 ≤ z.re) :
    ‖iteratedDeriv n (fun w : ℂ => jacobiTheta (I * w) - 1) z‖ ≤
      (n.factorial : ℝ) * (2 / (1 - Real.exp (-Real.pi / 2))) *
        Real.exp (-Real.pi * (z.re - 1 / 2)) / (1 / 2 : ℝ) ^ n := by
  have hp : 0 < 1 - Real.exp (-Real.pi / 2) := by
    have := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -Real.pi / 2 < 0)
    linarith
  have hgeom (w : ℂ) (hw : w ∈ Metric.closedBall z (1 / 2)) : z.re - 1 / 2 ≤ w.re := by
    have hd : ‖w - z‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have hr := (Complex.abs_re_le_norm (w - z)).trans hd
    have hh := (abs_le.mp hr).1
    simp only [Complex.sub_re] at hh
    linarith
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hd : DifferentiableOn ℂ (fun w : ℂ => jacobiTheta (I * w) - 1) {w : ℂ | 0 < w.re} := by
    intro w hw
    exact (((differentiableAt_jacobiTheta (by simpa using hw)).comp w
      (by fun_prop)).sub_const 1).differentiableWithinAt
  have hdiff : DiffContOnCl ℂ (fun w : ℂ => jacobiTheta (I * w) - 1)
      (Metric.ball z (1 / 2)) :=
    hd.diffContOnCl_ball (fun w hw => by change 0 < w.re; have := hgeom w hw; linarith)
  rw [mul_assoc (n.factorial : ℝ)]
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num) hdiff
  intro w hw
  have hg := hgeom w (Metric.sphere_subset_closedBall hw)
  have hwpos : 0 < w.re := by linarith
  calc
    _ ≤ (2 / (1 - Real.exp (-Real.pi * w.re))) * Real.exp (-Real.pi * w.re) := by
      simpa using norm_jacobiTheta_sub_one_le (τ := I * w) (by simpa using hwpos)
    _ ≤ (2 / (1 - Real.exp (-Real.pi / 2))) * Real.exp (-Real.pi * (z.re - 1 / 2)) := by
      have hr : 1 / 2 ≤ w.re := by linarith
      have hex : Real.exp (-Real.pi * w.re) ≤ Real.exp (-Real.pi / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos]
      apply mul_le_mul
      · apply div_le_div_of_nonneg_left (by norm_num) hp
        linarith
      · apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos]
      · positivity
      · positivity

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem theta_kernel_bound540 (z : ℂ) (hz : 1 ≤ z.re) :
    ‖thetaMellinKernel540 z‖ ≤
      (8 * ‖z‖ ^ 2 + 3 * ‖z‖) * (2 / (1 - Real.exp (-Real.pi / 2))) *
        Real.exp (-Real.pi * (z.re - 1 / 2)) := by
  let T : ℂ → ℂ := fun w => jacobiTheta (I * w)
  have hd : deriv (fun w => T w - 1) = deriv T := by
    ext w
    exact deriv_sub_const 1
  have hdd : iteratedDeriv 2 (fun w => T w - 1) = iteratedDeriv 2 T := by
    simp only [iteratedDeriv_succ', iteratedDeriv_one]
    rw [hd]
  have h1 := theta_cauchy_bound540 1 z hz
  have h2 := theta_cauchy_bound540 2 z hz
  rw [iteratedDeriv_one] at h1
  change ‖deriv (fun w => T w - 1) z‖ ≤ _ at h1
  rw [hd] at h1
  change ‖iteratedDeriv 2 (fun w => T w - 1) z‖ ≤ _ at h2
  rw [hdd] at h2
  norm_num at h1 h2
  have hn : ‖(3 / 2 : ℂ)‖ = (3 / 2 : ℝ) := by norm_num
  calc
    _ ≤ ‖z‖ ^ 2 * ‖iteratedDeriv 2 T z‖ +
        (3 / 2 : ℝ) * ‖z‖ * ‖deriv T z‖ := by
      change ‖z ^ 2 * iteratedDeriv 2 T z + (3 / 2 : ℂ) * z * deriv T z‖ ≤ _
      calc
        _ ≤ ‖z ^ 2 * iteratedDeriv 2 T z‖ + ‖(3 / 2 : ℂ) * z * deriv T z‖ := norm_add_le _ _
        _ ≤ (‖z ^ 2‖ * ‖iteratedDeriv 2 T z‖) +
            (‖(3 / 2 : ℂ) * z‖ * ‖deriv T z‖) :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ = _ := by rw [Complex.norm_pow, Complex.norm_mul, hn]
    _ ≤ ‖z‖ ^ 2 * (8 * (2 / (1 - Real.exp (-Real.pi / 2))) * Real.exp (-Real.pi * (z.re - 1 / 2))) +
        (3 / 2 : ℝ) * ‖z‖ * (2 * (2 / (1 - Real.exp (-Real.pi / 2))) * Real.exp (-Real.pi * (z.re - 1 / 2))) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        convert h2 using 1 <;> ring
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        convert h1 using 1 <;> ring
    _ = _ := by ring

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem theta_ray_top540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    (fun x : ℝ => thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)))
      =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
  let c : ℝ := Real.cos φ
  let C : ℝ := 2 / (1 - Real.exp (-Real.pi / 2))
  have hc : 0 < c := Real.cos_pos_of_mem_Ioo (abs_lt.mp hφ)
  have hC : 0 < C := by
    apply div_pos (by norm_num)
    have := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -Real.pi / 2 < 0)
    linarith
  have ha : 0 < Real.pi * c := mul_pos Real.pi_pos hc
  have ht : Tendsto (fun x : ℝ => x ^ 4 * Real.exp (-(Real.pi * c) * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℕ) (Real.pi * c) ha
  have he : ∀ᶠ x : ℝ in atTop, x ^ 4 * Real.exp (-(Real.pi * c) * x) ≤ 1 :=
    (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun x hx => hx.le)
  refine Asymptotics.isBigO_iff.mpr ⟨11 * C * Real.exp (Real.pi / 2), ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (1 / c)), he] with x hx hex
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hxp : 0 < x := by linarith
  have hxc : 1 ≤ x * c := by
    have hh := (le_max_right 1 (1 / c)).trans hx
    exact (div_le_iff₀ hc).mp hh
  let z : ℂ := (x : ℂ) * Complex.exp ((φ : ℂ) * I)
  have hzr : z.re = x * c := by simp [z, c, Complex.exp_re]
  have hzn : ‖z‖ = x := by simp [z, norm_mul, Complex.norm_exp, abs_of_pos hxp]
  have hb := theta_kernel_bound540 z (by rwa [hzr])
  rw [hzr, hzn] at hb
  have hp : 8 * x ^ 2 + 3 * x ≤ 11 * x ^ 2 := by nlinarith
  have hExp : Real.exp (-Real.pi * (x * c - 1 / 2)) =
      Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * c) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfin : x ^ 2 * Real.exp (-(Real.pi * c) * x) ≤ x ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hxp.le, Real.rpow_two]
    rw [← one_div (x ^ 2)]
    apply (le_div_iff₀ (sq_pos_of_pos hxp)).mpr
    nlinarith [hex]
  calc
    _ ≤ (8 * x ^ 2 + 3 * x) * C * Real.exp (-Real.pi * (x * c - 1 / 2)) := hb
    _ ≤ (11 * x ^ 2) * C * Real.exp (-Real.pi * (x * c - 1 / 2)) := by gcongr
    _ = (11 * C * Real.exp (Real.pi / 2)) *
        (x ^ 2 * Real.exp (-(Real.pi * c) * x)) := by rw [hExp]; ring
    _ ≤ (11 * C * Real.exp (Real.pi / 2)) * x ^ (-(2 : ℝ)) := by gcongr
    _ = _ := by rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]

/-- Hardy 1914 page 1012 display 1, auxiliary differentiated modular identity. -/
theorem theta_modular540 (z : ℂ) (hz : 0 < z.re) :
    jacobiTheta (I * z) = z ^ ((-1 / 2 : ℝ) : ℂ) * jacobiTheta (I * z⁻¹) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  let τ : UpperHalfPlane := ⟨I * z, by simpa using hz⟩
  have hh := jacobiTheta_S_smul τ
  have hτ : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = I * z⁻¹ := by
    simp only [UpperHalfPlane.modular_S_smul, τ]
    field_simp
    simp [I_sq]
  have hc : -I * (τ : ℂ) = z := by dsimp [τ]; simp [← mul_assoc]
  rw [hτ, hc] at hh
  have hpow : z ^ ((-1 / 2 : ℝ) : ℂ) * z ^ (1 / 2 : ℂ) = 1 := by
    rw [← Complex.cpow_add _ _ hz0]
    norm_num
  rw [hh, ← mul_assoc, hpow, one_mul]

/-- Hardy 1914 page 1012 display 1, auxiliary differentiated modular identity. -/
theorem hasDerivAt_theta_modular540 (z : ℂ) (hz : 0 < z.re) :
    HasDerivAt (fun w : ℂ => jacobiTheta (I * w))
      (z ^ ((-1 / 2 : ℝ) : ℂ) *
        (-(jacobiTheta (I * z⁻¹)) / (2 * z) -
          deriv (fun w : ℂ => jacobiTheta (I * w)) z⁻¹ / z ^ 2)) z := by
  let T : ℂ → ℂ := fun w => jacobiTheta (I * w)
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  have hi : 0 < (z⁻¹).re := by simpa [Complex.inv_re] using div_pos hz (Complex.normSq_pos.mpr hz0)
  have hT : DifferentiableAt ℂ T z⁻¹ :=
    (differentiableAt_jacobiTheta (by simpa using hi)).comp z⁻¹ (by fun_prop)
  have hq := (hasDerivAt_id z).cpow_const (c := ((-1 / 2 : ℝ) : ℂ)) hslit
  have hcomp := hT.hasDerivAt.comp z (hasDerivAt_inv hz0)
  have hprod := hq.mul hcomp
  have he : T =ᶠ[𝓝 z] (fun w : ℂ => w ^ ((-1 / 2 : ℝ) : ℂ) * T w⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz] with w hw
    exact theta_modular540 w hw
  have hcp : z ^ (((-1 / 2 : ℝ) : ℂ) - 1) = z ^ ((-1 / 2 : ℝ) : ℂ) / z := by
    rw [Complex.cpow_sub _ _ hz0, Complex.cpow_one]
  apply HasDerivAt.congr_of_eventuallyEq (f := fun w : ℂ => w ^ ((-1 / 2 : ℝ) : ℂ) * T w⁻¹) ?_ he
  convert hprod using 1
  · ext w
    simp [Function.comp_def, id_eq]
  · simp only [Function.comp_apply, id_eq, one_mul, hcp]
    dsimp [T]
    push_cast
    field_simp
    ring

/-- Hardy 1914 page 1012 display 1, auxiliary differentiated modular identity. -/
theorem theta_kernel_modular540 (z : ℂ) (hz : 0 < z.re) :
    thetaMellinKernel540 z = z ^ ((-1 / 2 : ℝ) : ℂ) * thetaMellinKernel540 z⁻¹ := by
  let T : ℂ → ℂ := fun w => jacobiTheta (I * w)
  let q : ℂ → ℂ := fun w => w ^ ((-1 / 2 : ℝ) : ℂ)
  let A : ℂ → ℂ := fun w => -(T w⁻¹) / (2 * w) - deriv T w⁻¹ / w ^ 2
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hi : 0 < (z⁻¹).re := by simpa [Complex.inv_re] using div_pos hz (Complex.normSq_pos.mpr hz0)
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hT : DifferentiableOn ℂ T {w : ℂ | 0 < w.re} := by
    intro w hw
    exact ((differentiableAt_jacobiTheta (by simpa using hw)).comp w (by fun_prop)).differentiableWithinAt
  have hT0 := (hT.differentiableAt (ho.mem_nhds hi)).hasDerivAt.comp z (hasDerivAt_inv hz0)
  have hT1 := ((hT.deriv ho).differentiableAt (ho.mem_nhds hi)).hasDerivAt.comp z (hasDerivAt_inv hz0)
  have hA := ((hT0.neg).div ((hasDerivAt_id z).const_mul 2) (mul_ne_zero (by norm_num) hz0)).sub
    (hT1.div ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz0))
  have hq := (hasDerivAt_id z).cpow_const (c := ((-1 / 2 : ℝ) : ℂ))
    (Complex.mem_slitPlane_iff.mpr (Or.inl hz))
  have hprod := hq.mul hA
  have he : deriv T =ᶠ[𝓝 z] (fun w : ℂ => q w * A w) := by
    filter_upwards [ho.mem_nhds hz] with w hw
    exact (hasDerivAt_theta_modular540 w hw).deriv
  have hcp : z ^ (((-1 / 2 : ℝ) : ℂ) - 1) = q z / z := by
    rw [Complex.cpow_sub _ _ hz0, Complex.cpow_one]
  have hp : HasDerivAt (fun w : ℂ => q w * A w)
      (q z * (3 * T z⁻¹ / (4 * z ^ 2) + 3 * deriv T z⁻¹ / z ^ 3 +
        deriv (deriv T) z⁻¹ / z ^ 4)) z := by
    convert hprod using 1
    · ext w
      simp [q, A, Function.comp_def]
    · simp only [Function.comp_apply, id_eq, mul_one, hcp, Pi.sub_apply, Pi.div_apply,
        Pi.neg_apply, Pi.pow_apply, Nat.cast_ofNat, pow_one]
      dsimp [A, q]
      push_cast
      field_simp
      ring
  have hsecond := hp.congr_of_eventuallyEq he
  have hfirst := (hasDerivAt_theta_modular540 z hz).deriv
  change deriv T z = q z * A z at hfirst
  unfold thetaMellinKernel540
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  change z ^ 2 * deriv (deriv T) z + (3 / 2 : ℂ) * z * deriv T z =
    q z * ((z⁻¹) ^ 2 * deriv (deriv T) z⁻¹ + (3 / 2 : ℂ) * z⁻¹ * deriv T z⁻¹)
  rw [hsecond.deriv, hfirst]
  dsimp [A, q]
  field_simp
  ring

/-- Hardy 1914 page 1012 display 1, the proved differentiated modular identity on an interior ray. -/
theorem theta_ray_modular540 (φ x : ℝ) (hφ : |φ| < Real.pi / 2) (hx : 0 < x) :
    thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)) =
      ((x : ℂ) * Complex.exp ((φ : ℂ) * I)) ^ ((-1 / 2 : ℝ) : ℂ) *
        thetaMellinKernel540 ((x⁻¹ : ℝ) * Complex.exp (((-φ : ℝ) : ℂ) * I)) := by
  have hh := theta_kernel_modular540 _ (ray_positive_re540 φ x hφ hx)
  have hi : ((x : ℂ) * Complex.exp ((φ : ℂ) * I))⁻¹ =
      (x⁻¹ : ℝ) * Complex.exp (((-φ : ℝ) : ℂ) * I) := by
    simp only [mul_inv_rev, ← Complex.exp_neg, Complex.ofReal_inv, Complex.ofReal_neg, neg_mul]
    ring
  simpa only [hi] using hh



/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem theta_ray_zero540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    (fun x : ℝ => thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)))
      =O[𝓝[>] 0] (fun x : ℝ => x ^ (-( -1 : ℝ))) := by
  have hneg : |-φ| < Real.pi / 2 := by simpa using hφ
  obtain ⟨C, hC, htop⟩ := Asymptotics.isBigO_iff'.mp (theta_ray_top540 (-φ) hneg)
  have hinv := (tendsto_inv_nhdsGT_zero.eventually htop)
  refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [hinv, self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with x ht hx hx1
  have hxp : 0 < x := hx
  rw [theta_ray_modular540 φ x hφ hxp, norm_mul, Complex.norm_cpow_real]
  have hnorm : ‖(x : ℂ) * Complex.exp ((φ : ℂ) * I)‖ = x := by
    simp [Complex.norm_exp, abs_of_pos hxp]
  rw [hnorm]
  have hpow : (x⁻¹) ^ (-(2 : ℝ)) = x ^ (2 : ℝ) := by
    rw [Real.inv_rpow hxp.le, ← Real.rpow_neg hxp.le, neg_neg]
  have hbound : x ^ (-1 / 2 : ℝ) * ‖thetaMellinKernel540 ((x⁻¹ : ℝ) *
      Complex.exp (((-φ : ℝ) : ℂ) * I))‖ ≤ C * x ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ x ^ (-1 / 2 : ℝ) * (C * ‖(x⁻¹) ^ (-(2 : ℝ))‖) :=
        mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hxp.le _)
      _ = C * (x ^ (-1 / 2 : ℝ) * x ^ (2 : ℝ)) := by
        rw [hpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]
        ring
      _ = _ := by rw [← Real.rpow_add hxp]; norm_num
  have hsmall : x ^ (3 / 2 : ℝ) ≤ x ^ (1 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_ge hxp hx1.le (by norm_num)
  calc
    _ ≤ C * x ^ (3 / 2 : ℝ) := hbound
    _ ≤ C * x ^ (1 : ℝ) := mul_le_mul_of_nonneg_left hsmall hC.le
    _ = _ := by simp only [neg_neg, Real.rpow_one, Real.norm_eq_abs, abs_of_pos hxp]

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem integrable_theta_ray540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    IntegrableOn (fun x : ℝ => x ^ (-3 / 4 : ℝ) *
      ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖) (Ioi 0) := by
  have hc := continuousOn_theta_ray540 φ hφ
  have hm := mellinConvergent_of_isBigO_rpow
    (s := (1 / 4 : ℂ)) (a := 2) (b := -1)
    (hc.locallyIntegrableOn measurableSet_Ioi) (theta_ray_top540 φ hφ)
    (by norm_num) (theta_ray_zero540 φ hφ) (by norm_num)
  have hi := (mellin_convergent_iff_norm (s := (1 / 4 : ℂ))
    Subset.rfl measurableSet_Ioi (hc.aestronglyMeasurable measurableSet_Ioi)).mp hm
  convert hi using 1 <;> norm_num

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
noncomputable def hardyAmplitude540 (t : ℝ) : ℝ :=
  -(1 / 2 : ℝ) *
    (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem continuous_hardyAmplitude540 : Continuous hardyAmplitude540 := by
  have hc : Continuous fun t : ℝ =>
      (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := by
    refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun t => ?_)
    apply ContinuousAt.comp (differentiableAt_completedZeta ?_ ?_).continuousAt (by fun_prop)
    all_goals
      intro h
      have := congrArg Complex.re h
      norm_num at this
  exact hc.const_mul _

/-- Hardy 1914 page 1012, the displayed definition of Xi. -/
noncomputable def hardyXi515 (t : ℝ) : ℝ :=
  -((1 / 4 : ℝ) + t ^ 2) / 2 *
    (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re

/-- Hardy 1914 page 1013 displays 2 and 3, smoothness from the exponential majorant. -/
theorem contDiffOn_expMoment540 (f : ℝ → ℝ) (hf : Continuous f) (φ C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ C * Real.exp (-φ * t))
    (m n : ℕ) : ContDiffOn ℝ m (expMoment540 f n) {α : ℝ | |α| < φ} := by
  have ho : IsOpen {α : ℝ | |α| < φ} := isOpen_lt continuous_abs continuous_const
  have hd (k : ℕ) : DifferentiableOn ℝ (expMoment540 f k) {α : ℝ | |α| < φ} := by
    intro α hα
    exact (hasDerivAt_expMoment540 f hf φ C hC hbound k α hα).differentiableAt.differentiableWithinAt
  induction m generalizing n with
  | zero => exact contDiffOn_zero.mpr (hd n).continuousOn
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : WithTop ENat) = (m : WithTop ENat) + 1 by simp]
    apply (contDiffOn_succ_iff_deriv_of_isOpen ho).mpr
    refine ⟨hd n, by simp, ?_⟩
    exact (ih (n + 1)).congr fun α hα =>
      (hasDerivAt_expMoment540 f hf φ C hC hbound n α hα).deriv

/-- Hardy 1914 page 1012 display 1, the Mathlib theta Mellin form in its convergence region. -/
theorem completedZeta_theta_mellin540 (w : ℂ) (hw : 1 / 2 < w.re) :
    completedRiemannZeta (2 * w) =
      mellin (fun x : ℝ => jacobiTheta (I * (x : ℂ)) - 1) w / 2 := by
  have hk (x : ℝ) : (HurwitzZeta.evenKernel 0 x : ℂ) = jacobiTheta (I * (x : ℂ)) := by
    simpa [jacobiTheta_eq_jacobiTheta₂] using HurwitzZeta.evenKernel_def 0 x
  have h := ((HurwitzZeta.hurwitzEvenFEPair 0).hasMellin (s := w) hw).2
  change (HurwitzZeta.hurwitzEvenFEPair 0).Λ (2 * w / 2) / 2 = _
  rw [show (2 : ℂ) * w / 2 = w by ring, ← h]
  congr 1
  congr 1
  ext x
  simp [HurwitzZeta.hurwitzEvenFEPair, hk]


/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem mellin_euler_derivative540 (f f' : ℝ → ℂ) (s : ℂ) (hs : s ≠ 0)
    (hf : ∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x)
    (hfi : MellinConvergent f s)
    (hdi : MellinConvergent (fun x : ℝ => (x : ℂ) * f' x) s)
    (hzero : Tendsto (fun x : ℝ => (x : ℂ) ^ s * f x) (𝓝[>] 0) (𝓝 0))
    (htop : Tendsto (fun x : ℝ => (x : ℂ) ^ s * f x) atTop (𝓝 0)) :
    mellin (fun x : ℝ => (x : ℂ) * f' x) s = -s * mellin f s := by
  have hpow (x : ℝ) (hx : 0 < x) : (x : ℂ) ^ (s - 1) * (x : ℂ) = (x : ℂ) ^ s := by
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hh := Complex.cpow_add (s - 1) 1 hx0
    simpa only [sub_add_cancel, Complex.cpow_one] using hh.symm
  have hi1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * f' x) (Ioi 0) := by
    apply hdi.congr_fun _ measurableSet_Ioi
    intro x hx
    simp only [smul_eq_mul]
    rw [← mul_assoc, hpow x hx]
  have hi2 : IntegrableOn (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * f x) (Ioi 0) := by
    have hi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * f x) (Ioi 0) := by
      simpa only [MellinConvergent, smul_eq_mul] using hfi
    simpa only [IntegrableOn, mul_assoc] using hi.const_mul s
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => (x : ℂ) ^ s) (u' := fun x : ℝ => s * (x : ℂ) ^ (s - 1))
    (v := f) (v' := f') (a' := (0 : ℂ)) (b' := (0 : ℂ))
    (fun x hx => hasDerivAt_ofReal_cpow_const hx.ne' hs)
    (fun x hx => hf x hx) hi1 hi2 hzero htop
  simp only [sub_zero, zero_sub] at h
  calc
    _ = ∫ x : ℝ in Ioi 0, (x : ℂ) ^ s * f' x := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [smul_eq_mul]
      rw [← mul_assoc, hpow x hx]
    _ = -(∫ x : ℝ in Ioi 0, (s * (x : ℂ) ^ (s - 1)) * f x) := h
    _ = -s * mellin f s := by
      rw [mellin, ← integral_neg, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [smul_eq_mul]
      ring

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_log_sector_rectangle540 (s : ℂ) (a b φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    let F : ℂ → ℂ := fun z => Complex.exp (s * z) * thetaMellinKernel540 (Complex.exp z)
    (∫ x : ℝ in a..b, F (x : ℂ)) - (∫ x : ℝ in a..b, F ((x : ℂ) + (φ : ℂ) * I)) +
      I * (∫ y : ℝ in 0..φ, F ((b : ℂ) + (y : ℂ) * I)) -
      I * (∫ y : ℝ in 0..φ, F ((a : ℂ) + (y : ℂ) * I)) = 0 := by
  dsimp only
  let F : ℂ → ℂ := fun z => Complex.exp (s * z) * thetaMellinKernel540 (Complex.exp z)
  have hdiff : DifferentiableOn ℂ F (Complex.Rectangle (a : ℂ) ((b : ℂ) + (φ : ℂ) * I)) := by
    intro z hz
    have him : z.im ∈ uIcc 0 φ := by simpa [Complex.Rectangle] using hz.2
    have hi : |z.im| ≤ |φ| := by
      rcases mem_uIcc.mp him with h | h
      · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]
        exact h.2
      · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]
        linarith [h.1]
    have hr : 0 < (Complex.exp z).re := by
      rw [Complex.exp_re]
      exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp (hi.trans_lt hφ)))
    have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
    have hk := differentiableOn_thetaMellinKernel540.differentiableAt (ho.mem_nhds hr)
    exact ((by fun_prop : DifferentiableAt ℂ (fun u => Complex.exp (s * u)) z).mul
      (hk.comp z (by fun_prop))).differentiableWithinAt
  simpa [F, Complex.Rectangle, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F (a : ℂ)
      ((b : ℂ) + (φ : ℂ) * I) hdiff

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_sector_top540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ v : ℝ, |v| ≤ |φ| →
      ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((v : ℂ) * I))‖ ≤ C * x ^ (-(2 : ℝ)) := by
  let c : ℝ := Real.cos φ
  let C : ℝ := 2 / (1 - Real.exp (-Real.pi / 2))
  have hc : 0 < c := Real.cos_pos_of_mem_Ioo (abs_lt.mp hφ)
  have hC : 0 < C := by
    apply div_pos (by norm_num)
    have := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -Real.pi / 2 < 0)
    linarith
  have ha : 0 < Real.pi * c := mul_pos Real.pi_pos hc
  have ht : Tendsto (fun x : ℝ => x ^ 4 * Real.exp (-(Real.pi * c) * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℕ) (Real.pi * c) ha
  have he : ∀ᶠ x : ℝ in atTop, x ^ 4 * Real.exp (-(Real.pi * c) * x) ≤ 1 :=
    (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun x hx => hx.le)
  refine ⟨11 * C * Real.exp (Real.pi / 2), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (1 / c)), he] with x hx hex
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hxp : 0 < x := by linarith
  have hxc : 1 ≤ x * c := by
    have hh := (le_max_right 1 (1 / c)).trans hx
    exact (div_le_iff₀ hc).mp hh
  intro v hv
  have hvcos : c ≤ Real.cos v := by
    dsimp [c]
    rw [← Real.cos_abs φ, ← Real.cos_abs v]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hv
  let z : ℂ := (x : ℂ) * Complex.exp ((v : ℂ) * I)
  have hzr : x * c ≤ z.re := by simpa [z, Complex.exp_re] using mul_le_mul_of_nonneg_left hvcos hxp.le
  have hzn : ‖z‖ = x := by simp [z, norm_mul, Complex.norm_exp, abs_of_pos hxp]
  have hb := theta_kernel_bound540 z (hxc.trans hzr)
  rw [hzn] at hb
  have hbe : Real.exp (-Real.pi * (z.re - 1 / 2)) ≤ Real.exp (-Real.pi * (x * c - 1 / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hb' : ‖thetaMellinKernel540 z‖ ≤
      (8 * x ^ 2 + 3 * x) * C * Real.exp (-Real.pi * (x * c - 1 / 2)) := by
    exact hb.trans (mul_le_mul_of_nonneg_left hbe (by positivity))
  have hp : 8 * x ^ 2 + 3 * x ≤ 11 * x ^ 2 := by nlinarith
  have hExp : Real.exp (-Real.pi * (x * c - 1 / 2)) =
      Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * c) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfin : x ^ 2 * Real.exp (-(Real.pi * c) * x) ≤ x ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hxp.le, Real.rpow_two]
    rw [← one_div (x ^ 2)]
    apply (le_div_iff₀ (sq_pos_of_pos hxp)).mpr
    nlinarith [hex]
  calc
    _ ≤ (8 * x ^ 2 + 3 * x) * C * Real.exp (-Real.pi * (x * c - 1 / 2)) := hb'
    _ ≤ (11 * x ^ 2) * C * Real.exp (-Real.pi * (x * c - 1 / 2)) := by gcongr
    _ = (11 * C * Real.exp (Real.pi / 2)) *
        (x ^ 2 * Real.exp (-(Real.pi * c) * x)) := by rw [hExp]; ring
    _ ≤ (11 * C * Real.exp (Real.pi / 2)) * x ^ (-(2 : ℝ)) := by gcongr

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_sector_zero540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in 𝓝[>] 0, ∀ v : ℝ, |v| ≤ |φ| →
      ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((v : ℂ) * I))‖ ≤ C * x := by
  obtain ⟨C, hC, htop⟩ := theta_sector_top540 φ hφ
  have hinv := (tendsto_inv_nhdsGT_zero.eventually htop)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hinv, self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with x ht hx hx1
  have hxp : 0 < x := hx
  intro v hv
  have hvφ : |v| < Real.pi / 2 := hv.trans_lt hφ
  have ht' := ht (-v) (by simpa using hv)
  rw [theta_ray_modular540 v x hvφ hxp, norm_mul, Complex.norm_cpow_real]
  have hnorm : ‖(x : ℂ) * Complex.exp ((v : ℂ) * I)‖ = x := by
    simp [Complex.norm_exp, abs_of_pos hxp]
  rw [hnorm]
  have hpow : (x⁻¹) ^ (-(2 : ℝ)) = x ^ (2 : ℝ) := by
    rw [Real.inv_rpow hxp.le, ← Real.rpow_neg hxp.le, neg_neg]
  have hbound : x ^ (-1 / 2 : ℝ) * ‖thetaMellinKernel540 ((x⁻¹ : ℝ) *
      Complex.exp (((-v : ℝ) : ℂ) * I))‖ ≤ C * x ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ x ^ (-1 / 2 : ℝ) * (C * (x⁻¹) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left ht' (Real.rpow_nonneg hxp.le _)
      _ = C * (x ^ (-1 / 2 : ℝ) * x ^ (2 : ℝ)) := by
        rw [hpow]
        ring
      _ = _ := by rw [← Real.rpow_add hxp]; norm_num
  have hsmall : x ^ (3 / 2 : ℝ) ≤ x ^ (1 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_ge hxp hx1.le (by norm_num)
  calc
    _ ≤ C * x ^ (3 / 2 : ℝ) := hbound
    _ ≤ C * x ^ (1 : ℝ) := mul_le_mul_of_nonneg_left hsmall hC.le
    _ = _ := by rw [Real.rpow_one]

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_log_arc_bound540 (φ t u C k : ℝ) (hC : 0 ≤ C)
    (hK : ∀ v ∈ uIcc 0 φ,
      ‖thetaMellinKernel540 (Complex.exp ((u : ℂ) + (v : ℂ) * I))‖ ≤ C * Real.exp (k * u)) :
    ‖∫ v : ℝ in 0..φ, Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) *
      ((u : ℂ) + (v : ℂ) * I)) * thetaMellinKernel540 (Complex.exp ((u : ℂ) + (v : ℂ) * I))‖ ≤
      (C * Real.exp (|t| * |φ|) * Real.exp ((k + 1 / 4) * u)) * |φ| := by
  have hint : ∀ v ∈ uIoc 0 φ,
      ‖Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) * ((u : ℂ) + (v : ℂ) * I)) *
        thetaMellinKernel540 (Complex.exp ((u : ℂ) + (v : ℂ) * I))‖ ≤
          C * Real.exp (|t| * |φ|) * Real.exp ((k + 1 / 4) * u) := by
    intro v hv
    have habs : |v| ≤ |φ| := by simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hv)
    have htv : -t * v ≤ |t| * |φ| := by
      calc
        _ = -(t * v) := by ring
        _ ≤ |t * v| := neg_le_abs _
        _ = |t| * |v| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    have hphase : ‖Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) *
        ((u : ℂ) + (v : ℂ) * I))‖ = Real.exp (u / 4 - t * v) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [norm_mul, hphase]
    calc
      _ ≤ Real.exp (u / 4 + |t| * |φ|) * (C * Real.exp (k * u)) :=
        mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hK v (uIoc_subset_uIcc hv))
          (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by
        rw [Real.exp_add, ← mul_assoc]
        rw [show u / 4 = (1 / 4 : ℝ) * u by ring,
          show (k + 1 / 4) * u = (1 / 4 : ℝ) * u + k * u by ring, Real.exp_add]
        ring
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const hint

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_log_outer_arc540 (φ t : ℝ) (hφ : |φ| < Real.pi / 2) :
    Tendsto (fun R : ℝ => ∫ v : ℝ in 0..φ,
      Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) * ((R : ℂ) + (v : ℂ) * I)) *
        thetaMellinKernel540 (Complex.exp ((R : ℂ) + (v : ℂ) * I))) atTop (𝓝 0) := by
  obtain ⟨C, hC, htop⟩ := theta_sector_top540 φ hφ
  have he := Real.tendsto_exp_atTop.eventually htop
  have hbound : ∀ᶠ R : ℝ in atTop,
      ‖∫ v : ℝ in 0..φ, Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) * ((R : ℂ) + (v : ℂ) * I)) *
        thetaMellinKernel540 (Complex.exp ((R : ℂ) + (v : ℂ) * I))‖ ≤
      C * Real.exp (|t| * |φ|) * Real.exp (-(7 / 4 : ℝ) * R) * |φ| := by
    filter_upwards [he] with R hR
    have hK (v : ℝ) (hv : v ∈ uIcc 0 φ) :
        ‖thetaMellinKernel540 (Complex.exp ((R : ℂ) + (v : ℂ) * I))‖ ≤ C * Real.exp (-2 * R) := by
      have hb := hR v (by simpa using abs_sub_left_of_mem_uIcc hv)
      have hp : (Real.exp R) ^ (-(2 : ℝ)) = Real.exp (-2 * R) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 1
        ring
      simpa only [Complex.exp_add, Complex.ofReal_exp, hp] using hb
    have hb := theta_log_arc_bound540 φ t R C (-2) hC.le hK
    convert hb using 1 <;> norm_num
  have hlim : Tendsto (fun R : ℝ => C * Real.exp (|t| * |φ|) *
      Real.exp (-(7 / 4 : ℝ) * R) * |φ|) atTop (𝓝 0) := by
    have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (7 / 4 : ℝ) (by norm_num)
    simpa only [Real.rpow_zero, one_mul, mul_zero, zero_mul] using
      (hh.const_mul (C * Real.exp (|t| * |φ|))).mul_const |φ|
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) hbound hlim)

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_log_inner_arc540 (φ t : ℝ) (hφ : |φ| < Real.pi / 2) :
    Tendsto (fun R : ℝ => ∫ v : ℝ in 0..φ,
      Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) * (((-R : ℝ) : ℂ) + (v : ℂ) * I)) *
        thetaMellinKernel540 (Complex.exp (((-R : ℝ) : ℂ) + (v : ℂ) * I))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hzero⟩ := theta_sector_zero540 φ hφ
  have he := (Real.tendsto_exp_atBot_nhdsGT.comp tendsto_neg_atTop_atBot).eventually hzero
  have hbound : ∀ᶠ R : ℝ in atTop,
      ‖∫ v : ℝ in 0..φ, Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) * (((-R : ℝ) : ℂ) + (v : ℂ) * I)) *
        thetaMellinKernel540 (Complex.exp (((-R : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
      C * Real.exp (|t| * |φ|) * Real.exp (-(5 / 4 : ℝ) * R) * |φ| := by
    filter_upwards [he] with R hR
    have hK (v : ℝ) (hv : v ∈ uIcc 0 φ) :
        ‖thetaMellinKernel540 (Complex.exp (((-R : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ C * Real.exp (1 * -R) := by
      have hb := hR v (by simpa using abs_sub_left_of_mem_uIcc hv)
      simpa only [Function.comp_apply, Complex.exp_add, Complex.ofReal_exp, one_mul] using hb
    have hb := theta_log_arc_bound540 φ t (-R) C 1 hC.le hK
    convert hb using 1 <;> ring
  have hlim : Tendsto (fun R : ℝ => C * Real.exp (|t| * |φ|) *
      Real.exp (-(5 / 4 : ℝ) * R) * |φ|) atTop (𝓝 0) := by
    have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (5 / 4 : ℝ) (by norm_num)
    simpa only [Real.rpow_zero, one_mul, mul_zero, zero_mul] using
      (hh.const_mul (C * Real.exp (|t| * |φ|))).mul_const |φ|
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) hbound hlim)

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem mellin_ray_log_integrand540 (w : ℂ) (φ u : ℝ) :
    Complex.exp (w * ((u : ℂ) + (φ : ℂ) * I)) *
      thetaMellinKernel540 (Complex.exp ((u : ℂ) + (φ : ℂ) * I)) =
    Complex.exp ((φ : ℂ) * I * w) *
      ((Real.exp u : ℂ) * ((Real.exp u : ℂ) ^ (w - 1) *
        thetaMellinKernel540 ((Real.exp u : ℂ) * Complex.exp ((φ : ℂ) * I)))) := by
  have hp : (Real.exp u : ℂ) ^ (w - 1) = Complex.exp ((u : ℂ) * (w - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  have he : Complex.exp (w * ((u : ℂ) + (φ : ℂ) * I)) =
      Complex.exp ((φ : ℂ) * I * w) * (Real.exp u : ℂ) * (Real.exp u : ℂ) ^ (w - 1) := by
    rw [hp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp]
  ring

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem mellin_ray_log540 (w : ℂ) (φ : ℝ) :
    (∫ u : ℝ, Complex.exp (w * ((u : ℂ) + (φ : ℂ) * I)) *
      thetaMellinKernel540 (Complex.exp ((u : ℂ) + (φ : ℂ) * I))) =
    Complex.exp ((φ : ℂ) * I * w) *
      ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (w - 1) *
        thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)) := by
  let g : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) *
    thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))
  rw [← integral_comp_exp g, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  simpa only [g, Complex.real_smul] using mellin_ray_log_integrand540 w φ u

/-- Hardy 1914 page 1012 display 1, proved sector rotation of the corrected theta Mellin integral. -/
theorem theta_mellin_rotate540 (φ t : ℝ) (hφ : |φ| < Real.pi / 2) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1) *
      thetaMellinKernel540 (x : ℂ)) =
    Complex.exp ((φ : ℂ) * I * ((1 / 4 : ℂ) + (t : ℂ) * I)) *
    ∫ x : ℝ in Ioi 0, (x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1) *
      thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)) := by
  let w : ℂ := (1 / 4 : ℂ) + (t : ℂ) * I
  let F : ℂ → ℂ := fun z => Complex.exp (w * z) * thetaMellinKernel540 (Complex.exp z)
  have hlog (ψ : ℝ) (hψ : |ψ| < Real.pi / 2) :
      Integrable (fun u : ℝ => F ((u : ℂ) + (ψ : ℂ) * I)) := by
    let g : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) *
      thetaMellinKernel540 ((x : ℂ) * Complex.exp ((ψ : ℂ) * I))
    have hc := continuousOn_theta_ray540 ψ hψ
    have hm := mellinConvergent_of_isBigO_rpow (s := w) (a := 2) (b := -1)
      (hc.locallyIntegrableOn measurableSet_Ioi) (theta_ray_top540 ψ hψ)
      (by dsimp [w]; norm_num) (theta_ray_zero540 ψ hψ) (by dsimp [w]; norm_num)
    have hg : IntegrableOn g (Ioi 0) := by
      simpa only [MellinConvergent, smul_eq_mul, g] using hm
    have hi := ((integrable_comp_exp g).mpr hg).const_mul (Complex.exp ((ψ : ℂ) * I * w))
    apply hi.congr
    filter_upwards [] with u
    simpa only [F, g, Complex.real_smul] using (mellin_ray_log_integrand540 w ψ u).symm
  have h0 := hlog 0 (by simpa using (by positivity : (0 : ℝ) < Real.pi / 2))
  have hφint := hlog φ hφ
  have hA := intervalIntegral_tendsto_integral h0 tendsto_neg_atTop_atBot tendsto_id
  have hB := intervalIntegral_tendsto_integral hφint tendsto_neg_atTop_atBot tendsto_id
  have hout := theta_log_outer_arc540 φ t hφ
  have hin := theta_log_inner_arc540 φ t hφ
  have hlim := ((hA.sub hB).add (hout.const_mul I)).sub (hin.const_mul I)
  simp only [mul_zero, add_zero, sub_zero] at hlim
  have hconst : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop
      (𝓝 ((∫ u : ℝ, F ((u : ℂ) + (0 : ℂ) * I)) -
        ∫ u : ℝ, F ((u : ℂ) + (φ : ℂ) * I))) := by
    apply hlim.congr'
    filter_upwards [] with R
    simpa only [id_eq, F, w, Complex.ofReal_zero, zero_mul, add_zero] using
      theta_log_sector_rectangle540 w (-R) R φ hφ
  have heq := sub_eq_zero.mp (tendsto_nhds_unique hconst tendsto_const_nhds)
  change (∫ u : ℝ, Complex.exp (w * ((u : ℂ) + (0 : ℂ) * I)) *
      thetaMellinKernel540 (Complex.exp ((u : ℂ) + (0 : ℂ) * I))) =
    (∫ u : ℝ, Complex.exp (w * ((u : ℂ) + (φ : ℂ) * I)) *
      thetaMellinKernel540 (Complex.exp ((u : ℂ) + (φ : ℂ) * I))) at heq
  have hz := mellin_ray_log540 w 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.exp_zero, one_mul, mul_one] at hz
  simp only [zero_mul, add_zero] at heq
  rw [hz, mellin_ray_log540 w φ] at heq
  simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] using heq

/-- Hardy 1914 page 1012, the unshifted theta contour at real part one. -/
noncomputable def hardyUnshifted540 (α : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-(α : ℂ) * I * ((1 : ℂ) + (t : ℂ) * I)) *
    completedRiemannZeta (2 * ((1 : ℂ) + (t : ℂ) * I))

/-- LEAF Hardy 1914 page 1012, the unshifted display before display 1.
The line has real part one and the theta parameter has positive real part.
This is the unshifted complex theta transform, before crossing the pole. -/
theorem hardy_unshifted_theta540 (α : ℝ) (hα : |α| < Real.pi / 2) :
    hardyUnshifted540 α = (Real.pi : ℂ) *
      (jacobiTheta (I * Complex.exp ((α : ℂ) * I)) - 1) := by
  sorry

/-- LEAF Hardy 1914 page 1012 display 1 and page 1013 display 2.
Shift the completed zeta contour from real part one to one quarter.
The residue at one half gives pi cosine. Pair the two critical line half rays.
Uniform horizontal bounds for every intermediate real part remain required. -/
theorem hardy_shifted_contour540 (α : ℝ) (hα : |α| < Real.pi / 2) :
    (Complex.exp ((α : ℂ) * I / 4) * hardyUnshifted540 α).re =
      Real.pi * Real.cos (α / 4) - 2 * expMoment540 hardyAmplitude540 0 α := by
  sorry

/-- Hardy 1914 page 1012 display 1, auxiliary obstruction to absolute termwise Mellin integration.
The critical line Gaussian power series has exponent one half and is not summable.
This is a bound obstruction and is not a question about the paper. -/
theorem not_summable_theta_half_power540 :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 / 2 : ℝ)) := by
  have he : (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 / 2 : ℝ)) =
      (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (1 / 2 : ℝ)) := by
    ext n
    rw [abs_of_nonneg (by positivity)]
  rw [he, Real.summable_one_div_nat_add_rpow]
  norm_num

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_raw_bounds540 :
    ((fun x : ℝ => jacobiTheta (I * (x : ℂ)) - 1) =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ)))) ∧
    ((fun x : ℝ => jacobiTheta (I * (x : ℂ)) - 1) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))) := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  have hk (x : ℝ) : (HurwitzZeta.evenKernel 0 x : ℂ) = jacobiTheta (I * (x : ℂ)) := by
    simpa [jacobiTheta_eq_jacobiTheta₂] using HurwitzZeta.evenKernel_def 0 x
  have he : (fun x : ℝ => P.f x - P.f₀) = (fun x : ℝ => jacobiTheta (I * (x : ℂ)) - 1) := by
    ext x
    simp [P, HurwitzZeta.hurwitzEvenFEPair, hk]
  constructor
  · rw [← he]
    exact P.hf_top (-2)
  · rw [← he]
    exact P.hf_zero'

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_euler_top540 :
    (fun x : ℝ => (x : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ))
      =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
  let C : ℝ := 2 / (1 - Real.exp (-Real.pi / 2))
  have hC : 0 < C := by
    apply div_pos (by norm_num)
    have := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -Real.pi / 2 < 0)
    linarith
  have hlim : Tendsto (fun x : ℝ => x ^ 3 * Real.exp (-Real.pi * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℕ) Real.pi Real.pi_pos
  have he : ∀ᶠ x : ℝ in atTop, x ^ 3 * Real.exp (-Real.pi * x) ≤ 1 :=
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono fun x hx => hx.le
  have hd : deriv (fun w : ℂ => jacobiTheta (I * w) - 1) =
      deriv (fun w : ℂ => jacobiTheta (I * w)) := by
    ext w
    exact deriv_sub_const 1
  refine Asymptotics.isBigO_iff.mpr ⟨2 * C * Real.exp (Real.pi / 2), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), he] with x hx hex
  have hxp : 0 < x := by linarith
  have hb := theta_cauchy_bound540 1 (x : ℂ) hx
  rw [iteratedDeriv_one, hd] at hb
  norm_num at hb
  have hbound : ‖deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ)‖ ≤
      2 * C * Real.exp (-Real.pi * (x - 1 / 2)) := by dsimp [C]; convert hb using 1 <;> ring
  have hfin : x * Real.exp (-Real.pi * x) ≤ x ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hxp.le, Real.rpow_two, ← one_div]
    apply (le_div_iff₀ (sq_pos_of_pos hxp)).mpr
    nlinarith [hex]
  calc
    _ = x * ‖deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxp]
    _ ≤ x * (2 * C * Real.exp (-Real.pi * (x - 1 / 2))) :=
      mul_le_mul_of_nonneg_left hbound hxp.le
    _ = (2 * C * Real.exp (Real.pi / 2)) * (x * Real.exp (-Real.pi * x)) := by
      rw [show -Real.pi * (x - 1 / 2) = Real.pi / 2 + -Real.pi * x by ring, Real.exp_add]
      ring
    _ ≤ (2 * C * Real.exp (Real.pi / 2)) * x ^ (-(2 : ℝ)) := by gcongr
    _ = _ := by rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_euler_zero540 :
    (fun x : ℝ => (x : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ))
      =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Cf, hCf, hf⟩ := Asymptotics.isBigO_iff'.mp theta_raw_bounds540.1
  obtain ⟨Cd, hCd, hd⟩ := Asymptotics.isBigO_iff'.mp theta_euler_top540
  have hfi := tendsto_inv_nhdsGT_zero.eventually hf
  have hdi := tendsto_inv_nhdsGT_zero.eventually hd
  have hy := tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop (1 : ℝ))
  refine Asymptotics.isBigO_iff.mpr ⟨(Cf + 1) / 2 + Cd, ?_⟩
  filter_upwards [hfi, hdi, hy, self_mem_nhdsWithin] with x hfx hdx hyx hx
  have hxp : 0 < x := hx
  have hp : (x⁻¹) ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hyx (by norm_num)
  have hpn : ‖(x⁻¹) ^ (-(2 : ℝ))‖ ≤ 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hxp.le) _)]
  have hfb : ‖jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ)) - 1‖ ≤ Cf := by
    simpa only [mul_one] using hfx.trans (mul_le_mul_of_nonneg_left hpn hCf.le)
  have hdb : ‖((x⁻¹ : ℝ) : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) ((x⁻¹ : ℝ) : ℂ)‖ ≤ Cd := by
    simpa only [mul_one] using hdx.trans (mul_le_mul_of_nonneg_left hpn hCd.le)
  have htheta : ‖jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ))‖ ≤ Cf + 1 := by
    calc
      _ = ‖(jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ)) - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ)) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ _ := by simpa using add_le_add_right hfb 1
  have hform : (x : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ) =
      (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) *
        (-(jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ))) / 2 -
          ((x⁻¹ : ℝ) : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) ((x⁻¹ : ℝ) : ℂ)) := by
    rw [(hasDerivAt_theta_modular540 (x : ℂ) hxp).deriv]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hxp.ne'] <;> ring
  have hrest : ‖-(jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ))) / 2 -
      ((x⁻¹ : ℝ) : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) ((x⁻¹ : ℝ) : ℂ)‖ ≤ (Cf + 1) / 2 + Cd := by
    apply (norm_sub_le _ _).trans
    rw [norm_div, norm_neg]
    norm_num only [Complex.norm_ofNat]
    exact add_le_add (div_le_div_of_nonneg_right htheta (by norm_num)) hdb
  rw [hform, norm_mul, Complex.norm_cpow_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hxp, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]
  simpa only [neg_div, mul_comm] using
    mul_le_mul_of_nonneg_left hrest (Real.rpow_nonneg hxp.le (-1 / 2))

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_weighted_boundary540 (f : ℝ → ℂ)
    (htop : f =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))))
    (hzero : f =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(1 / 2 : ℝ))))
    (w : ℂ) (hw1 : 1 / 2 < w.re) (hw2 : w.re < 2) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ w * f x) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x : ℂ) ^ w * f x) (𝓝[>] 0) (𝓝 0) := by
  have general (l : Filter ℝ) (r : ℝ) (hpos : ∀ᶠ x : ℝ in l, 0 < x)
      (hf : f =O[l] (fun x : ℝ => x ^ r))
      (hr : Tendsto (fun x : ℝ => x ^ (w.re + r)) l (𝓝 0)) :
      Tendsto (fun x : ℝ => (x : ℂ) ^ w * f x) l (𝓝 0) := by
    obtain ⟨C, hC, hb⟩ := Asymptotics.isBigO_iff'.mp hf
    have he : ∀ᶠ x : ℝ in l, ‖(x : ℂ) ^ w * f x‖ ≤ C * x ^ (w.re + r) := by
      filter_upwards [hb, hpos] with x hx hxp
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxp]
      calc
        _ ≤ x ^ w.re * (C * ‖x ^ r‖) :=
          mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hxp.le _)
        _ = C * x ^ (w.re + r) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _), Real.rpow_add hxp]
          ring
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) he
        (by simpa only [mul_zero] using hr.const_mul C))
  constructor
  · apply general atTop (-2) (eventually_gt_atTop 0) htop
    rw [show w.re + -(2 : ℝ) = -(2 - w.re) by ring]
    exact tendsto_rpow_neg_atTop (show 0 < 2 - w.re by linarith)
  · apply general (𝓝[>] 0) (-(1 / 2)) self_mem_nhdsWithin hzero
    have hp : 0 < w.re + -(1 / 2 : ℝ) := by linarith
    have hh0 : Tendsto (fun x : ℝ => x ^ (w.re + -(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa only [Real.zero_rpow hp.ne'] using (Real.continuous_rpow_const hp.le).tendsto (0 : ℝ)
    exact hh0.mono_left nhdsWithin_le_nhds

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_kernel_mellin_right540 (w : ℂ) (hw1 : 1 / 2 < w.re) (hw2 : w.re < 2) :
    mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w =
      2 * w * (w - 1 / 2) * completedRiemannZeta (2 * w) := by
  let T : ℂ → ℂ := fun z => jacobiTheta (I * z)
  let G : ℝ → ℂ := fun x => T (x : ℂ) - 1
  let E : ℝ → ℂ := fun x => (x : ℂ) * deriv T (x : ℂ)
  let E' : ℝ → ℂ := fun x => deriv T (x : ℂ) + (x : ℂ) * deriv (deriv T) (x : ℂ)
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw1; linarith
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hT : DifferentiableOn ℂ T {z : ℂ | 0 < z.re} := by
    intro z hz
    exact ((differentiableAt_jacobiTheta (by simpa using hz)).comp z (by fun_prop)).differentiableWithinAt
  have hfG (x : ℝ) (hx : 0 < x) : HasDerivAt G (deriv T (x : ℂ)) x := by
    exact ((hT.differentiableAt (ho.mem_nhds hx)).hasDerivAt.sub_const 1).comp_ofReal
  have hfE (x : ℝ) (hx : 0 < x) : HasDerivAt E (E' x) x := by
    have hh := ((hasDerivAt_id (x : ℂ)).mul
      ((hT.deriv ho).differentiableAt (ho.mem_nhds hx)).hasDerivAt).comp_ofReal
    simpa only [E, E', Pi.mul_apply, id_eq, one_mul] using hh
  have hmG : MellinConvergent G w := mellinConvergent_of_isBigO_rpow
    ((continuousOn_of_forall_continuousAt fun x hx => (hfG x hx).continuousAt).locallyIntegrableOn measurableSet_Ioi)
    theta_raw_bounds540.1 hw2 theta_raw_bounds540.2 hw1
  have hmE : MellinConvergent E w := mellinConvergent_of_isBigO_rpow
    ((continuousOn_of_forall_continuousAt fun x hx => (hfE x hx).continuousAt).locallyIntegrableOn measurableSet_Ioi)
    theta_euler_top540 hw2 theta_euler_zero540 hw1
  have hangle : |(0 : ℝ)| < Real.pi / 2 := by simpa using (by positivity : (0 : ℝ) < Real.pi / 2)
  have hcK : ContinuousOn (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) (Ioi 0) := by
    simpa using continuousOn_theta_ray540 0 hangle
  have htK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
    simpa using theta_ray_top540 0 hangle
  have hzK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(-1 : ℝ))) := by
    simpa using theta_ray_zero540 0 hangle
  have hmK : MellinConvergent (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w :=
    mellinConvergent_of_isBigO_rpow (hcK.locallyIntegrableOn measurableSet_Ioi) htK hw2 hzK (by linarith)
  have hiK : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * thetaMellinKernel540 (x : ℂ)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hmK
  have hiE : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * E x) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hmE
  have hiD : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * ((x : ℂ) * E' x)) (Ioi 0) := by
    apply (hiK.sub (hiE.const_mul (1 / 2 : ℂ))).congr_fun _ measurableSet_Ioi
    intro x hx
    dsimp only [E, E', T, thetaMellinKernel540]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Pi.sub_apply, Pi.mul_apply]
    ring
  have hmD : MellinConvergent (fun x : ℝ => (x : ℂ) * E' x) w := by
    simpa only [MellinConvergent, smul_eq_mul] using hiD
  have hBG := theta_weighted_boundary540 G theta_raw_bounds540.1 theta_raw_bounds540.2 w hw1 hw2
  have hBE := theta_weighted_boundary540 E theta_euler_top540 theta_euler_zero540 w hw1 hw2
  have hP0 := mellin_euler_derivative540 G (fun x : ℝ => deriv T (x : ℂ)) w hw0 hfG hmG hmE hBG.2 hBG.1
  have hP1 := mellin_euler_derivative540 E E' w hw0 hfE hmE hmD hBE.2 hBE.1
  have hlin : mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w =
      mellin (fun x : ℝ => (x : ℂ) * E' x) w + (1 / 2 : ℂ) * mellin E w := by
    unfold mellin
    simp only [smul_eq_mul]
    rw [← integral_const_mul, ← integral_add hiD (hiE.const_mul (1 / 2 : ℂ))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [E, E', T, thetaMellinKernel540]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Pi.sub_apply, Pi.mul_apply]
    ring
  have hM0 : completedRiemannZeta (2 * w) = mellin G w / 2 := completedZeta_theta_mellin540 w hw1
  rw [hlin, hP1, hP0, hM0]
  ring

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_kernel_mellin_strip540 (w : ℂ) (hw0 : -1 < w.re) (hw2 : w.re < 2) :
    mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w =
      2 * w * (w - 1 / 2) * completedRiemannZeta₀ (2 * w) + 1 / 2 := by
  let U : Set ℂ := {z | -1 < z.re ∧ z.re < 2}
  let M : ℂ → ℂ := mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ))
  let F : ℂ → ℂ := fun z => 2 * z * (z - 1 / 2) * completedRiemannZeta₀ (2 * z) + 1 / 2
  have hangle : |(0 : ℝ)| < Real.pi / 2 := by simpa using (by positivity : (0 : ℝ) < Real.pi / 2)
  have hcK : ContinuousOn (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) (Ioi 0) := by
    simpa using continuousOn_theta_ray540 0 hangle
  have htK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
    simpa using theta_ray_top540 0 hangle
  have hzK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(-1 : ℝ))) := by
    simpa using theta_ray_zero540 0 hangle
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have hcv : Convex ℝ U := (convex_Ioo (-1 : ℝ) 2).linear_preimage Complex.reCLM.toLinearMap
  have hM : DifferentiableOn ℂ M U := by
    intro z hz
    exact (mellin_differentiableAt_of_isBigO_rpow
      (hcK.locallyIntegrableOn measurableSet_Ioi) htK hz.2 hzK hz.1).differentiableWithinAt
  have hcomp : Differentiable ℂ (fun z : ℂ => completedRiemannZeta₀ (2 * z)) :=
    differentiable_completedZeta₀.comp (by fun_prop)
  have hF : Differentiable ℂ F := by
    dsimp [F]
    fun_prop
  have hright (z : ℂ) (hz1 : 1 / 2 < z.re) (hz2 : z.re < 2) : M z = F z := by
    have hs0 : 2 * z ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      norm_num at hh
      linarith
    have hs1 : 1 - 2 * z ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      norm_num at hh
      linarith
    change mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) z = _
    rw [theta_kernel_mellin_right540 z hz1 hz2, completedRiemannZeta_eq]
    dsimp [F]
    have hz0 : z ≠ 0 := by intro h; simp [h] at hs0
    field_simp [hs0, hs1, hz0] <;> ring
  have hnear : M =ᶠ[𝓝 (1 : ℂ)] F := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re),
      (isOpen_lt continuous_re continuous_const).mem_nhds
        (by norm_num : (1 : ℂ).re < (2 : ℝ))] with z hz1 hz2
    exact hright z hz1 hz2
  exact (hM.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (hF.differentiableOn.analyticOnNhd hU) hcv.isPreconnected (show (1 : ℂ) ∈ U by norm_num [U]) hnear ⟨hw0, hw2⟩

/-- Hardy 1914 page 1012 display 1, the corrected theta Mellin representation of Xi.
Two integrations by parts and analytic uniqueness prove the critical exponent identity. -/
theorem theta_xi_mellin540 (t : ℝ) :
    (-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) *
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I) =
    ∫ x : ℝ in Ioi 0, (x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1) *
      thetaMellinKernel540 (x : ℂ) := by
  let w : ℂ := (1 / 4 : ℂ) + (t : ℂ) * I
  have hm := theta_kernel_mellin_strip540 w (by norm_num [w]) (by norm_num [w])
  have hw0 : w ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [w] at hh
  have hw1 : 1 - 2 * w ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [w] at hh
  have hs : (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I = 2 * w := by
    dsimp [w]
    push_cast
    ring
  have hp : (-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) = 2 * w * (w - 1 / 2) := by
    dsimp [w]
    push_cast
    apply Complex.ext <;> simp [pow_two] <;> ring
  rw [hs, hp]
  calc
    _ = 2 * w * (w - 1 / 2) * completedRiemannZeta₀ (2 * w) + 1 / 2 := by
      rw [completedRiemannZeta_eq]
      field_simp [hw0, hw1] <;> ring
    _ = mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w := hm.symm
    _ = _ := rfl


/-- Hardy 1914 page 1012 display 1, proved exponential decay from the theta Mellin sector. -/
theorem theta_xi_decay540 (φ t : ℝ) (hφ : |φ| < Real.pi / 2) :
    ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) *
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤
    Real.exp (-φ * t) *
      ∫ x : ℝ in Ioi 0, x ^ (-3 / 4 : ℝ) *
        ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖ := by
  rw [theta_xi_mellin540, theta_mellin_rotate540 φ t hφ, norm_mul,
    mellin_ray_phase_norm540]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    _ ≤ ∫ x : ℝ in Ioi 0,
        ‖(x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1) *
          thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [norm_mul, mellin_ray_power_norm540 x t hx]

/-- Hardy 1914 page 1012 display 1, proved exponential decay from the theta Mellin sector. -/
theorem hardyAmplitude_decay540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      |hardyAmplitude540 t| ≤ C * Real.exp (-φ * t) := by
  let A : ℝ := ∫ x : ℝ in Ioi 0, x ^ (-3 / 4 : ℝ) *
    ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖
  have hA : 0 ≤ A := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)
  refine ⟨4 * (A + 1), by linarith, ?_⟩
  intro t ht
  let L : ℂ := completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)
  have hD : (1 / 8 : ℝ) * ‖L‖ ≤ ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) * L‖ := by
    rw [norm_mul]
    have hnorm : ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ)‖ =
        ((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 := by
      norm_cast
      rw [Real.norm_eq_abs, abs_of_nonpos (by nlinarith [sq_nonneg (2 * t)])]
      ring
    rw [hnorm]
    nlinarith [sq_nonneg (2 * t), norm_nonneg L]
  have hreal : |hardyAmplitude540 t| ≤ (1 / 2 : ℝ) * ‖L‖ := by
    change |-(1 / 2 : ℝ) * L.re| ≤ _
    calc
      _ = (1 / 2 : ℝ) * |L.re| := by rw [abs_mul]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm L) (by norm_num)
  have hd := theta_xi_decay540 φ t hφ
  change ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) * L‖ ≤ Real.exp (-φ * t) * A at hd
  have he : 0 < Real.exp (-φ * t) := Real.exp_pos _
  nlinarith

/-- Hardy 1914 page 1012 display 1, proved exponential decay from the theta Mellin sector. -/
theorem hardyXi_decay540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      |hardyXi515 (2 * t)| ≤ C * Real.exp (-φ * t) := by
  let A : ℝ := ∫ x : ℝ in Ioi 0, x ^ (-3 / 4 : ℝ) *
    ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖
  have hA : 0 ≤ A := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)
  refine ⟨A + 1, by linarith, ?_⟩
  intro t ht
  have hp : (((-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℝ)) : ℂ) =
      (-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) := by push_cast; rfl
  have hr : |hardyXi515 (2 * t)| ≤ ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) *
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ := by
    rw [hardyXi515, abs_mul, norm_mul, ← hp, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
  have hd := theta_xi_decay540 φ t hφ
  change ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) *
    completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤ Real.exp (-φ * t) * A at hd
  have he := Real.exp_pos (-φ * t)
  exact hr.trans (hd.trans (by nlinarith))

end LeanLab.BhowmikGrimmelt2026
