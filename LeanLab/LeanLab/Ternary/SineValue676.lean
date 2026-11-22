/-
Abramowitz and Stegun https://personal.math.ubc.ca/~cbm/aands/page_232.htm
Page 232 equation 5.2.25. Dirichlet kernel proof of the sine integral value.
The finite kernel and defect estimates are derived steps of this proof.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
open Real MeasureTheory Set Filter
open scoped Topology

namespace LeanLab.Ternary.Task676

/-- The finite odd Dirichlet kernel identity.
Derived trigonometric step for page 232 equation 5.2.25. -/
theorem kernel_mul_sin (n : ℕ) (x : ℝ) :
    Real.sin x * (1 + 2 * ∑ k ∈ Finset.range n,
      Real.cos (2 * ((k : ℝ) + 1) * x)) = Real.sin ((2 * (n : ℝ) + 1) * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have htrig : Real.sin ((2 * ((n : ℝ) + 1) + 1) * x) -
        Real.sin ((2 * (n : ℝ) + 1) * x) =
        2 * Real.sin x * Real.cos (2 * ((n : ℝ) + 1) * x) := by
      rw [show (2 * ((n : ℝ) + 1) + 1) * x = 2 * ((n : ℝ) + 1) * x + x by ring,
        show (2 * (n : ℝ) + 1) * x = 2 * ((n : ℝ) + 1) * x - x by ring,
        Real.sin_add, Real.sin_sub]
      ring
    nlinarith

/-- The finite odd Dirichlet kernel has half pi integral on the half interval.
Derived finite integral step for page 232 equation 5.2.25. -/
theorem kernel_integral (n : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
      1 + 2 * ∑ k ∈ Finset.range n, Real.cos (2 * ((k : ℝ) + 1) * x)) =
      Real.pi / 2 := by
  have hi (k : ℕ) : IntervalIntegrable
      (fun x : ℝ => Real.cos (2 * ((k : ℝ) + 1) * x)) volume 0 (Real.pi / 2) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.cos (2 * ((k : ℝ) + 1) * x))).intervalIntegrable _ _
  have hz (k : ℕ) : (∫ x in (0 : ℝ)..Real.pi / 2,
      Real.cos (2 * ((k : ℝ) + 1) * x)) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left _ (by positivity : 2 * ((k : ℝ) + 1) ≠ 0)]
    rw [integral_cos]
    have heq : 2 * ((k : ℝ) + 1) * (Real.pi / 2) = (k + 1 : ℕ) * Real.pi := by
      push_cast
      ring
    simp only [heq, mul_zero, Real.sin_zero, sub_zero]
    rw [show ((k + 1 : ℕ) : ℝ) * Real.pi = (k : ℝ) * Real.pi + Real.pi by push_cast; ring, Real.sin_add]
    simp
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (((by fun_prop : Continuous (fun x : ℝ => ∑ k ∈ Finset.range n, Real.cos (2 * ((k : ℝ) + 1) * x))).intervalIntegrable 0 (Real.pi / 2)).const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun k _ => hi k)]
  simp [hz]

/-- An interval integrable amplitude has vanishing high frequency sine integrals.
Mathlib Riemann Lebesgue lemma applied in the proof of page 232 equation 5.2.25. -/
theorem sine_interval_decay (g : ℝ → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hg : IntervalIntegrable g volume 0 a) :
    Tendsto (fun w : ℝ => ∫ x in (0 : ℝ)..a, g x * Real.sin (w * x))
      atTop (𝓝 0) := by
  let f : ℝ → ℂ := (Ioc 0 a).indicator (fun x => (g x : ℂ))
  have hf : Integrable f := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mp hg).ofReal
  have hw : Tendsto (fun w : ℝ => -w / (2 * Real.pi)) atTop (cocompact ℝ) := by
    have h := tendsto_neg_atTop_atBot.comp
      (tendsto_id.atTop_div_const (by positivity : 0 < 2 * Real.pi))
    have h' : Tendsto (fun w : ℝ => -w / (2 * Real.pi)) atTop atBot := by
      simpa only [Function.comp_def, neg_div, id_eq] using h
    exact h'.mono_right atBot_le_cocompact
  have hr := (Real.tendsto_integral_exp_smul_cocompact f).comp hw
  have heq (w : ℝ) :
      (∫ v : ℝ, Real.fourierChar (-(v * (-w / (2 * Real.pi)))) • f v).im =
        ∫ x in (0 : ℝ)..a, g x * Real.sin (w * x) := by
    have hi : Integrable (fun v : ℝ =>
        Real.fourierChar (-(v * (-w / (2 * Real.pi)))) • f v) := by
      have hi' := (Real.fourierIntegral_convergent_iff (μ := volume) (f := f)
        (-w / (2 * Real.pi))).2 hf
      simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using hi'
    have him : (∫ v : ℝ, Real.fourierChar (-(v * (-w / (2 * Real.pi)))) • f v).im =
        ∫ v : ℝ, (Real.fourierChar (-(v * (-w / (2 * Real.pi)))) • f v).im := by
      exact (Complex.imCLM.integral_comp_comm hi).symm
    rw [him, intervalIntegral.integral_of_le ha,
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    have halg : 2 * Real.pi * -(x * (-w / (2 * Real.pi))) = w * x := by
      field_simp
    have hc : (Real.fourierChar (-(x * (-w / (2 * Real.pi)))) : ℂ) =
        Complex.exp ((w * x : ℝ) * Complex.I) := by
      rw [Real.fourierChar_apply, halg]
    by_cases hx : x ∈ Ioc 0 a
    · simp only [f, Set.indicator_of_mem hx, Circle.smul_def, hc, smul_eq_mul,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_im, mul_zero]
      ring
    · simp [f, hx]
  have h := Complex.continuous_im.continuousAt.tendsto.comp hr
  simpa only [Function.comp_def, heq, Complex.zero_im] using h

/-- The totalized difference of reciprocal argument and reciprocal sine is bounded.
Derived Jordan inequality and Taylor estimate for page 232 equation 5.2.25. -/
theorem sine_defect_bound {x : ℝ} (hx : 0 ≤ x) (hxp : x ≤ Real.pi / 2) :
    |1 / x - 1 / Real.sin x| ≤ Real.pi ^ 2 / 24 := by
  obtain rfl | hx0 := hx.eq_or_lt
  · simp
    positivity
  have hsin : 0 < Real.sin x :=
    (mul_pos (by positivity : 0 < 2 / Real.pi) hx0).trans_le (Real.mul_le_sin hx hxp)
  rw [div_sub_div _ _ hx0.ne' hsin.ne', one_mul, mul_one, abs_div,
    abs_of_pos (mul_pos hx0 hsin)]
  have hnum : |Real.sin x - x| ≤ x ^ 3 / 6 := by
    simpa only [abs_sub_comm, abs_of_nonneg hx] using Real.abs_sub_sin_le x
  calc
    _ ≤ (x ^ 3 / 6) / (x * Real.sin x) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (x ^ 3 / 6) / (x * (2 / Real.pi * x)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left (Real.mul_le_sin hx hxp) hx)
    _ = Real.pi * x / 12 := by field_simp; ring
    _ ≤ _ := by nlinarith [Real.pi_pos]

/-- The reciprocal sine defect is integrable on the closed half interval.
Derived endpoint justification for page 232 equation 5.2.25. -/
theorem sine_defect_integrable :
    IntervalIntegrable (fun x : ℝ => 1 / x - 1 / Real.sin x)
      volume 0 (Real.pi / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  have hi : IntegrableOn (fun _ : ℝ => Real.pi ^ 2 / 24)
      (Ioc 0 (Real.pi / 2)) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply hi.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa only [Real.norm_eq_abs] using sine_defect_bound hx.1.le hx.2

/-- The sine integral at odd half pi equals the kernel mass plus the defect integral.
Derived finite comparison for page 232 equation 5.2.25. -/
theorem sine_kernel_identity (n : ℕ) :
    (∫ u in (0 : ℝ)..((2 * (n : ℝ) + 1) * (Real.pi / 2)), Real.sinc u) =
      Real.pi / 2 + ∫ x in (0 : ℝ)..Real.pi / 2,
        (1 / x - 1 / Real.sin x) * Real.sin ((2 * (n : ℝ) + 1) * x) := by
  let w : ℝ := 2 * (n : ℝ) + 1
  have hw : 0 < w := by dsimp [w]; positivity
  have hs := intervalIntegral.mul_integral_comp_mul_left (a := 0) (b := Real.pi / 2)
    (f := Real.sinc) w
  simp only [mul_zero] at hs
  change (∫ u in (0 : ℝ)..(w * (Real.pi / 2)), Real.sinc u) = _
  rw [← hs, ← intervalIntegral.integral_const_mul]
  have heq : (∫ x in (0 : ℝ)..Real.pi / 2, w * Real.sinc (w * x)) =
      ∫ x in (0 : ℝ)..Real.pi / 2,
        (1 + 2 * ∑ k ∈ Finset.range n, Real.cos (2 * ((k : ℝ) + 1) * x)) +
          (1 / x - 1 / Real.sin x) * Real.sin (w * x) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
    intro x hx
    have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
    have hk : 1 + 2 * ∑ k ∈ Finset.range n,
        Real.cos (2 * ((k : ℝ) + 1) * x) = Real.sin (w * x) / Real.sin x := by
      apply (eq_div_iff hsin.ne').mpr
      simpa only [w, mul_comm] using kernel_mul_sin n x
    dsimp only
    rw [hk, Real.sinc_of_ne_zero (mul_ne_zero hw.ne' hx.1.ne')]
    field_simp
    ring
  rw [heq, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun x : ℝ =>
      1 + 2 * ∑ k ∈ Finset.range n, Real.cos (2 * ((k : ℝ) + 1) * x))).intervalIntegrable _ _)
    (sine_defect_integrable.mul_continuousOn (by fun_prop)), kernel_integral]

/-- Every limit of the finite sine integrals equals half pi.
Abramowitz and Stegun page 232 equation 5.2.25. -/
theorem sine_integral_value (L : ℝ)
    (hL : Tendsto (fun x : ℝ => ∫ u in (0 : ℝ)..x, Real.sinc u) atTop (𝓝 L)) :
    L = Real.pi / 2 := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hm (n : ℕ) : (n : ℝ) ≤ 2 * (n : ℝ) + 1 := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hw : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono hm hn
  have he : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) * (Real.pi / 2)) atTop atTop :=
    hw.atTop_mul_const (by positivity)
  have hdecay := (sine_interval_decay (fun x : ℝ => 1 / x - 1 / Real.sin x)
    (by positivity : (0 : ℝ) ≤ Real.pi / 2) sine_defect_integrable).comp hw
  have hv : Tendsto
      (fun n : ℕ => ∫ u in (0 : ℝ)..((2 * (n : ℝ) + 1) * (Real.pi / 2)), Real.sinc u)
      atTop (𝓝 (Real.pi / 2)) := by
    simp_rw [sine_kernel_identity]
    simpa only [add_zero, Function.comp_def] using tendsto_const_nhds.add hdecay
  exact tendsto_nhds_unique (hL.comp he) hv

end LeanLab.Ternary.Task676
