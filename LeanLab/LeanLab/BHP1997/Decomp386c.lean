/-
P0069, page 25, the Perron kernel estimate between 4.3 and 4.4.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp386a

namespace LeanLab.BHP1997.Decomp386c
open Complex

/-- Page 25, the Perron window kernel is bounded uniformly over every height.
The bound uses only that the window stays above x divided by two. -/
theorem perron_kernel_bound {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyx : y ≤ x / 2) (t : ℝ) :
    ‖((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t‖ ≤
      (x / 2) ^ (-(1 / 2 : ℝ)) * y := by
  let s : ℂ := Thm4.half t
  have hs : s ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp [s, Thm4.half] at hre
  have hxy : 0 < x - y := by linarith
  have hd : ∀ u ∈ Set.Icc (x - y) x,
      HasDerivWithinAt (fun v : ℝ => (v : ℂ) ^ s / s)
        ((u : ℂ) ^ (s - 1)) (Set.Icc (x - y) x) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hxy.trans_le hu.1)
    have hr : s - 1 ≠ -1 := by intro h; apply hs; linear_combination h
    simpa only [sub_add_cancel] using
      (hasDerivAt_ofReal_cpow_const' hu0 hr).hasDerivWithinAt
  have hb : ∀ u ∈ Set.Ico (x - y) x,
      ‖(u : ℂ) ^ (s - 1)‖ ≤ (x / 2) ^ (-(1 / 2 : ℝ)) := by
    intro u hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hxy.trans_le hu.1)]
    have hre : (s - 1).re = -(1 / 2 : ℝ) := by simp [s, Thm4.half]; norm_num
    rw [hre]
    apply Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x / 2) (by linarith [hu.1] : x / 2 ≤ u)
    norm_num
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb x
    (show x ∈ Set.Icc (x - y) x from ⟨by linarith, le_rfl⟩)
  simpa only [← sub_div, sub_sub_cancel] using h

/-- Page 25, both high height pieces are bounded by the same kernel estimate.
This is the integral bookkeeping used with the two signs in display 4.1. -/
theorem two_tail_norm_bound (F K : ℝ → ℂ) (hF : Continuous F) (hK : Continuous K)
    {T0 T1 R M : ℝ} (hT : T0 ≤ T1) (hR : 0 ≤ R)
    (hkernel : ∀ t : ℝ, ‖K t‖ ≤ R)
    (hplus : (∫ t in T0..T1, ‖F t‖) ≤ M)
    (hminus : (∫ t in T0..T1, ‖F (-t)‖) ≤ M) :
    ‖(∫ t in (-T1)..T1, F t * K t) -
      ∫ t in (-T0)..T0, F t * K t‖ ≤ 2 * R * M := by
  have hprod : Continuous (fun t => F t * K t) := hF.mul hK
  have hbound {a b : ℝ} (hab : a ≤ b) :
      ‖∫ t in a..b, F t * K t‖ ≤ R * ∫ t in a..b, ‖F t‖ := by
    calc
      _ ≤ ∫ t in a..b, R * ‖F t‖ := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab
        · exact Filter.Eventually.of_forall (fun t ht => by
            rw [norm_mul]
            simpa only [mul_comm] using
              mul_le_mul_of_nonneg_left (hkernel t) (norm_nonneg (F t)))
        · exact (continuous_const.mul hF.norm).intervalIntegrable _ _
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hp := (hbound hT).trans (mul_le_mul_of_nonneg_left hplus hR)
  have hn : ‖∫ t in (-T1)..(-T0), F t * K t‖ ≤ R * M := by
    have he : (∫ t in (-T1)..(-T0), ‖F t‖) = ∫ t in T0..T1, ‖F (-t)‖ := by
      exact (intervalIntegral.integral_comp_neg (fun t => ‖F t‖) (a := T0) (b := T1)).symm
    exact (hbound (neg_le_neg hT)).trans
      (mul_le_mul_of_nonneg_left (he.trans_le hminus) hR)
  rw [intervalIntegral.integral_interval_sub_interval_comm'
    (hprod.intervalIntegrable _ _) (hprod.intervalIntegrable _ _) (hprod.intervalIntegrable _ _),
    intervalIntegral.integral_symm (-T1) (-T0), sub_neg_eq_add]
  have hnorm := norm_add_le
    (∫ t in T0..T1, F t * K t) (∫ t in (-T1)..(-T0), F t * K t)
  linarith

/-- Pages 24 and 25, the subexponential low height is eventually below every
fixed positive power height. -/
theorem eventually_low_height_le_power {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ α := by
  have hs : ∀ᶠ u : ℝ in Filter.atTop, u ^ (-(2 / 3 : ℝ)) < α :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).eventually
      (eventually_lt_nhds hα)
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have he : Real.log x ^ (1 / 3 : ℝ) = Real.log x * Real.log x ^ (-(2 / 3 : ℝ)) := by
    calc
      _ = Real.log x ^ ((1 : ℝ) + (-(2 / 3 : ℝ))) := by norm_num
      _ = _ := by rw [Real.rpow_add hl, Real.rpow_one]
  rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
  apply Real.exp_le_exp.mpr
  rw [he]
  exact mul_le_mul_of_nonneg_left hx.le hl.le

/-- Page 25, the first order expansion of the Perron window kernel.
This is the pointwise Taylor error used in display 4.4. -/
theorem perron_kernel_first_order_bound {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyx : y ≤ x / 2) (t : ℝ) :
    ‖((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t -
      (y : ℂ) * (x : ℂ) ^ (Thm4.half t - 1)‖ ≤
        ‖Thm4.half t - 1‖ * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2 := by
  let s : ℂ := Thm4.half t
  let H : ℝ := ‖s - 1‖ * (x / 2) ^ (-(3 / 2 : ℝ))
  have hs : s ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp [s, Thm4.half] at h'
  have hr : s - 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp [s, Thm4.half] at h'
    norm_num at h'
  have hxy : 0 < x - y := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hbound {u v : ℝ} (hu : x - y ≤ u) (hv : u ≤ v) :
      ‖(s - 1) * (v : ℂ) ^ (s - 1 - 1)‖ ≤ H := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < v)]
    have hre : (s - 1 - 1).re = -(3 / 2 : ℝ) := by simp [s, Thm4.half]; norm_num
    rw [hre]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x / 2)
      (by linarith : x / 2 ≤ v) (by norm_num)
  have hfirst : ∀ u ∈ Set.Icc (x - y) x,
      ‖(u : ℂ) ^ (s - 1) - (x : ℂ) ^ (s - 1)‖ ≤ H * y := by
    intro u hu
    have hd : ∀ v ∈ Set.Icc u x,
        HasDerivWithinAt (fun v : ℝ => (v : ℂ) ^ (s - 1))
          ((s - 1) * (v : ℂ) ^ (s - 1 - 1)) (Set.Icc u x) v := by
      intro v hv
      exact (hasDerivAt_ofReal_cpow_const (by linarith [hu.1, hv.1] : v ≠ 0) hr).hasDerivWithinAt
    have hb : ∀ v ∈ Set.Ico u x,
        ‖(s - 1) * (v : ℂ) ^ (s - 1 - 1)‖ ≤ H := by
      intro v hv
      exact hbound hu.1 hv.1
    have hh := norm_image_sub_le_of_norm_deriv_le_segment' hd hb x
      (show x ∈ Set.Icc u x from ⟨hu.2, le_rfl⟩)
    rw [norm_sub_rev] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hu.1]) hH)
  let g : ℝ → ℂ := fun u => (u : ℂ) ^ s / s - (u : ℂ) * (x : ℂ) ^ (s - 1)
  have hd : ∀ u ∈ Set.Icc (x - y) x,
      HasDerivWithinAt g ((u : ℂ) ^ (s - 1) - (x : ℂ) ^ (s - 1))
        (Set.Icc (x - y) x) u := by
    intro u hu
    have h0 : u ≠ 0 := by linarith [hu.1]
    have hn : s - 1 ≠ -1 := by intro h; apply hs; linear_combination h
    have hpower := hasDerivAt_ofReal_cpow_const' h0 hn
    have hlinear := ((hasDerivAt_id u).ofReal_comp).mul_const ((x : ℂ) ^ (s - 1))
    simpa only [g, Pi.sub_apply, id_eq, sub_add_cancel, Complex.ofReal_one, one_mul] using!
      (hpower.sub hlinear).hasDerivWithinAt
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun u hu => hfirst u (Set.Ico_subset_Icc_self hu)) x
    (show x ∈ Set.Icc (x - y) x from ⟨by linarith, le_rfl⟩)
  have he : g x - g (x - y) =
      ((x : ℂ) ^ s - ((x - y : ℝ) : ℂ) ^ s) / s -
        (y : ℂ) * (x : ℂ) ^ (s - 1) := by
    dsimp [g]
    push_cast
    ring
  rw [he] at hh
  simpa only [sub_sub_cancel, H, pow_two, mul_assoc] using hh

/-- Page 25, the low height exceeds every fixed power of log x eventually.
This is the logarithmic absorption used in display 4.4. -/
theorem eventually_log_power_le_low_height (D : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ D ≤ Real.exp (Real.log x ^ (1 / 3 : ℝ)) := by
  have hs : ∀ᶠ u : ℝ in Filter.atTop, D * Real.log u ≤ u ^ (1 / 3 : ℝ) := by
    filter_upwards [((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul_left D).bound
      (by norm_num : (0 : ℝ) < 1), Filter.eventually_ge_atTop (0 : ℝ)] with u hu hu0
    have h : |D * Real.log u| ≤ u ^ (1 / 3 : ℝ) := by
      simpa only [one_mul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hu0 _)] using hu
    exact (le_abs_self _).trans h
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    Real.tendsto_log_atTop.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with x hx hx0
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  nlinarith

end LeanLab.BHP1997.Decomp386c
