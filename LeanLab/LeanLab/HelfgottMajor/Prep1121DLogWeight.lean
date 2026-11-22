import LeanLab.HelfgottMajor.Prep1121VIIntegral

/-!
PREP 2026-11-21 deepening pass p2, route step `MainLemma41Split123.vertical_integral_bound`.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 35, the exact part
of the integral after display 4.12: ∫_ℝ log(τ² + 9/4)/(1/4 + τ²) dτ = 4π log 2. The paper
evaluates the whole integral numerically; the lab route needs this closed form. The parent
leaf `Prep1121VIIntegral.integral_log_weight` is proved here with its exact statement by
differentiation in the parameter b of G(b) = ∫ log(τ² + b²)/(1/4 + τ²) dτ: G'(b) = 4π/(1/2 + b)
for b above 1/2 by partial fractions, so G(b) - 4π log(1/2 + b) is constant on [3/2, ∞), and
it tends to 0 at infinity, so it vanishes at b = 3/2. The two former LEAF pieces are proved, ROUTE BURST S4 burst-20261122.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DLogWeight
open Real MeasureTheory Set Filter Topology

/-! ## Integrability helpers, ROUTE BURST S4 burst-20261122

Copies of the integrability lemmas of `Prep1121DIntegrable`, P0014 page 35, renamed with the
prefix dlw_ since this file does not import that module. AI wrote this Lean code. -/

/-- log(τ² + 9/4)²/(1/4 + τ²) ≤ 1000 (1 + |τ|)^(-3/2). -/
theorem dlw_log_sq_weight_le (τ : ℝ) :
    Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 1000 * (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) := by
  set t : ℝ := ‖τ‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg τ
  have hτ : τ ^ 2 = t ^ 2 := by rw [ht, Real.norm_eq_abs, sq_abs]
  set a : ℝ := 1 + t with ha
  have ha1 : 1 ≤ a := by linarith
  set c : ℝ := a ^ (1 / 8 : ℝ) with hc
  have hc1 : 1 ≤ c := Real.one_le_rpow ha1 (by norm_num)
  have hc0 : 0 ≤ c := by linarith
  have hc8 : c ^ 8 = a := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hc12 : a ^ (-(3 / 2 : ℝ)) = 1 / c ^ 12 := by
    rw [← hc8, ← Real.rpow_natCast, ← Real.rpow_mul hc0,
      show ((8 : ℕ) : ℝ) * (-(3 / 2)) = -((12 : ℕ) : ℝ) by norm_num, Real.rpow_neg hc0,
      Real.rpow_natCast]
    ring
  have hw : 0 < 1 / 4 + τ ^ 2 := by positivity
  have hx : 0 < τ ^ 2 + 9 / 4 := by positivity
  have hxa : τ ^ 2 + 9 / 4 ≤ 9 / 4 * a ^ 2 := by rw [hτ, ha]; nlinarith
  have hwa : a ^ 2 ≤ 8 * (1 / 4 + τ ^ 2) := by rw [hτ, ha]; nlinarith [sq_nonneg (t - 1)]
  have hℓ0 : 0 ≤ Real.log (τ ^ 2 + 9 / 4) := Real.log_nonneg (by nlinarith)
  have hloga : Real.log a = 8 * Real.log c := by rw [← hc8, Real.log_pow]; norm_num
  have hlogc : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hl94 : Real.log (9 / 4) ≤ 9 / 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hℓ : Real.log (τ ^ 2 + 9 / 4) ≤ 16 * c - 14.75 := by
    have h1 : Real.log (τ ^ 2 + 9 / 4) ≤ Real.log (9 / 4 * a ^ 2) :=
      Real.log_le_log hx hxa
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hloga] at h1
    push_cast at h1
    linarith
  have hsq : Real.log (τ ^ 2 + 9 / 4) ^ 2 ≤ (16 * c - 14.75) ^ 2 :=
    pow_le_pow_left₀ hℓ0 hℓ 2
  have hpoly : (16 * c - 14.75) ^ 2 ≤ 125 * c ^ 4 := by
    nlinarith [sq_nonneg (c ^ 2 - 2), sq_nonneg (c - 1), mul_nonneg (sub_nonneg.mpr hc1)
      (sub_nonneg.mpr hc1), sq_nonneg (c ^ 2 - 1)]
  have hc16 : c ^ 16 = a ^ 2 := by rw [← hc8]; ring
  rw [hc12, mul_one_div, div_le_div_iff₀ hw (by positivity)]
  have hc12p : 0 ≤ c ^ 12 := by positivity
  calc Real.log (τ ^ 2 + 9 / 4) ^ 2 * c ^ 12 ≤ (16 * c - 14.75) ^ 2 * c ^ 12 :=
        mul_le_mul_of_nonneg_right hsq hc12p
    _ ≤ 125 * c ^ 4 * c ^ 12 := mul_le_mul_of_nonneg_right hpoly hc12p
    _ = 125 * a ^ 2 := by rw [← hc16]; ring
    _ ≤ 1000 * (1 / 4 + τ ^ 2) := by linarith

/-- 1/(1/4 + τ²) is integrable on ℝ. -/
theorem dlw_integrable_weight : Integrable (fun τ : ℝ => 1 / (1 / 4 + τ ^ 2)) := by
  have h : (fun τ : ℝ => 1 / (1 / 4 + τ ^ 2)) = fun τ => 4 * (1 + (2 * τ) ^ 2)⁻¹ := by
    funext τ
    have : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
    have : (0 : ℝ) < 1 + (2 * τ) ^ 2 := by positivity
    field_simp
    ring
  rw [h]
  exact ((integrable_inv_one_add_sq).comp_mul_left' (two_ne_zero)).const_mul 4

/-- log(τ² + 9/4)²/(1/4 + τ²) is integrable on ℝ. -/
theorem dlw_integrable_log_sq_weight :
    Integrable (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) := by
  have hI : Integrable (fun τ : ℝ => (1 + ‖τ‖) ^ (-(3 / 2 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  refine (hI.const_mul 1000).mono' (Measurable.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact dlw_log_sq_weight_le τ

/-- log(τ² + 9/4)/(1/4 + τ²) is integrable on ℝ. -/
theorem dlw_integrable_log_weight :
    Integrable (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) / (1 / 4 + τ ^ 2)) := by
  refine (dlw_integrable_weight.add dlw_integrable_log_sq_weight).mono'
    (Measurable.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun τ => ?_)
  have hw : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
  set ℓ := Real.log (τ ^ 2 + 9 / 4)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hw]
  simp only [Pi.add_apply]
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ hw.le
  rcases abs_cases ℓ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
    nlinarith [sq_nonneg (ℓ - 1), sq_nonneg (ℓ + 1)]

/-- PROVED in ROUTE BURST S4 burst-20261122, formerly the LEAF piece. P0014 page 35, the exact part of the integral after display 4.12, step one:
differentiation under the integral sign in b, for b > 0,
d/db ∫ log(τ² + b²)/(1/4 + τ²) dτ = ∫ 2b/((τ² + b²)(1/4 + τ²)) dτ.
Class MEDIUM: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on a ball around b inside
(b/2, 2b), with the dominating function (4/b)/(1/4 + τ²) and integrability of
log(τ² + c²)/(1/4 + τ²), as in `Prep1121DIntegrable`. -/
theorem hasDerivAt_param (b : ℝ) (hb : 0 < b) :
    HasDerivAt (fun c : ℝ => ∫ τ : ℝ, Real.log (τ ^ 2 + c ^ 2) / (1 / 4 + τ ^ 2))
      (∫ τ : ℝ, 2 * b / ((τ ^ 2 + b ^ 2) * (1 / 4 + τ ^ 2))) b := by
  have hb2 : (0 : ℝ) < b / 2 := by linarith
  have hint : Integrable (fun τ : ℝ => Real.log (τ ^ 2 + b ^ 2) / (1 / 4 + τ ^ 2)) := by
    set K : ℝ := Real.log (1 + b ^ 2) + |2 * Real.log b|
    refine (dlw_integrable_log_weight.add (dlw_integrable_weight.const_mul K)).mono'
      (Measurable.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun τ => ?_)
    have hw : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
    have hy : 0 < τ ^ 2 + b ^ 2 := by positivity
    have hup : Real.log (τ ^ 2 + b ^ 2) ≤ Real.log (τ ^ 2 + 9 / 4) + Real.log (1 + b ^ 2) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      exact Real.log_le_log hy (by nlinarith [sq_nonneg τ, sq_nonneg b, sq_nonneg (τ * b)])
    have hlo : 2 * Real.log b ≤ Real.log (τ ^ 2 + b ^ 2) := by
      rw [show 2 * Real.log b = Real.log (b ^ 2) by rw [Real.log_pow]; norm_num]
      exact Real.log_le_log (by positivity) (by nlinarith [sq_nonneg τ])
    have h94 : 0 ≤ Real.log (τ ^ 2 + 9 / 4) := Real.log_nonneg (by nlinarith [sq_nonneg τ])
    have h1b : 0 ≤ Real.log (1 + b ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg b])
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hw]
    simp only [Pi.add_apply]
    rw [mul_one_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hw.le
    have := neg_abs_le (2 * Real.log b)
    have := le_abs_self (2 * Real.log b)
    rw [abs_le]
    constructor <;> linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (c : ℝ) (τ : ℝ) => Real.log (τ ^ 2 + c ^ 2) / (1 / 4 + τ ^ 2))
    (F' := fun (c : ℝ) (τ : ℝ) => 2 * c / ((τ ^ 2 + c ^ 2) * (1 / 4 + τ ^ 2)))
    (x₀ := b) (bound := fun τ => 4 / b * (1 / (1 / 4 + τ ^ 2)))
    (Metric.ball_mem_nhds b hb2)
    (Filter.Eventually.of_forall fun c => Measurable.aestronglyMeasurable (by fun_prop))
    hint (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    (dlw_integrable_weight.const_mul _) ?_
  · exact key.2
  · refine Filter.Eventually.of_forall fun τ x hx => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    have hx0 : b / 2 < x := by linarith
    have hxp : 0 < x := by linarith
    have hw : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
    have hy : 0 < τ ^ 2 + x ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hw]
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]
    have : 2 * x * b ≤ 4 * (τ ^ 2 + x ^ 2) := by nlinarith [sq_nonneg τ]
    nlinarith
  · refine Filter.Eventually.of_forall fun τ x hx => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    have hxp : 0 < x := by linarith
    have hy : 0 < τ ^ 2 + x ^ 2 := by positivity
    have h1 : HasDerivAt (fun c : ℝ => τ ^ 2 + c ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add (τ ^ 2))
    have h2 := ((h1.log hy.ne').div_const (1 / 4 + τ ^ 2))
    convert h2 using 1
    field_simp

/-- 1/(τ² + c²) = c⁻² (1 + (τ/c)²)⁻¹. -/
theorem inv_sq_add_eq (c : ℝ) (hc : 0 < c) :
    (fun τ : ℝ => 1 / (τ ^ 2 + c ^ 2)) = fun τ => (c⁻¹) ^ 2 * (1 + (τ / c) ^ 2)⁻¹ := by
  funext τ
  have : 0 < τ ^ 2 + c ^ 2 := by positivity
  field_simp
  ring

/-- 1/(τ² + c²) is integrable on ℝ for c > 0. -/
theorem integrable_inv_sq_add (c : ℝ) (hc : 0 < c) :
    Integrable (fun τ : ℝ => 1 / (τ ^ 2 + c ^ 2)) := by
  rw [inv_sq_add_eq c hc]
  exact ((integrable_inv_one_add_sq).comp_div hc.ne').const_mul _

/-- ∫ dτ/(τ² + c²) = π/c for c > 0, from `integral_univ_inv_one_add_sq`. -/
theorem integral_inv_sq_add (c : ℝ) (hc : 0 < c) :
    ∫ τ : ℝ, 1 / (τ ^ 2 + c ^ 2) = π / c := by
  rw [inv_sq_add_eq c hc, integral_const_mul,
    Measure.integral_comp_div (fun y : ℝ => (1 + y ^ 2)⁻¹) c, integral_univ_inv_one_add_sq,
    abs_of_pos hc, smul_eq_mul]
  field_simp

/-- P0014 page 35, the exact part of the integral after display 4.12, step two:
partial fractions, for b > 1/2,
2b/((τ² + b²)(1/4 + τ²)) = (2b/(b² - 1/4)) (1/(1/4 + τ²) - 1/(τ² + b²)), and
∫ dτ/(τ² + c²) = π/c, so the integral is (2b/(b² - 1/4)) (2π - π/b) = 4π/(1/2 + b).
PROVED here from `integral_inv_sq_add` and `integral_sub`. -/
theorem integral_partial_fraction (b : ℝ) (hb : 1 / 2 < b) :
    ∫ τ : ℝ, 2 * b / ((τ ^ 2 + b ^ 2) * (1 / 4 + τ ^ 2)) = 4 * π / (1 / 2 + b) := by
  have hb0 : 0 < b := by linarith
  have hk : b ^ 2 - 1 / 4 ≠ 0 := by nlinarith
  have hk' : -1 + b ^ 2 * 4 ≠ 0 := by nlinarith
  have hk'' : 4 * b ^ 2 - 1 ≠ 0 := by nlinarith
  have h : (fun τ : ℝ => 2 * b / ((τ ^ 2 + b ^ 2) * (1 / 4 + τ ^ 2))) = fun τ =>
      2 * b / (b ^ 2 - 1 / 4) * (1 / (τ ^ 2 + (1 / 2) ^ 2) - 1 / (τ ^ 2 + b ^ 2)) := by
    funext τ
    have : 0 < τ ^ 2 + b ^ 2 := by positivity
    have : 0 < 1 / 4 + τ ^ 2 := by positivity
    have : 0 < τ ^ 2 + (1 / 2) ^ 2 := by positivity
    field_simp
    linear_combination (-(1 + τ ^ 2 * 4)) * mul_inv_cancel₀ hk'
  rw [h, integral_const_mul, integral_sub (integrable_inv_sq_add _ (by norm_num))
    (integrable_inv_sq_add _ hb0), integral_inv_sq_add _ (by norm_num), integral_inv_sq_add _ hb0]
  have h1 : (0 : ℝ) < 1 / 2 + b := by linarith
  have h2 : b - 1 / 2 ≠ 0 := by linarith
  field_simp
  linear_combination mul_inv_cancel₀ hk'

/-- PROVED in ROUTE BURST S4 burst-20261122, formerly the LEAF piece. P0014 page 35, the exact part of the integral after display 4.12, step three:
∫ log(τ² + c²)/(1/4 + τ²) dτ - 4π log(1/2 + c) tends to 0 as c → ∞. Writing
log(τ² + c²) = 2 log c + log(1 + τ²/c²) and ∫ 1/(1/4 + τ²) = 2π, the difference is
∫ log(1 + τ²/c²)/(1/4 + τ²) dτ + 4π (log c - log(1/2 + c)); the first term tends to 0 by
dominated convergence with the bound log(1 + τ²)/(1/4 + τ²) for c ≥ 1, the second by
continuity of log at 1. Class MEDIUM: `tendsto_integral_filter_of_dominated_convergence`. -/
theorem tendsto_param :
    Tendsto (fun c : ℝ => (∫ τ : ℝ, Real.log (τ ^ 2 + c ^ 2) / (1 / 4 + τ ^ 2)) -
      4 * π * Real.log (1 / 2 + c)) atTop (𝓝 0) := by
  have hwI : ∫ τ : ℝ, 1 / (1 / 4 + τ ^ 2) = 2 * π := by
    have := integral_inv_sq_add (1 / 2) (by norm_num)
    have e : (fun τ : ℝ => 1 / (1 / 4 + τ ^ 2)) = fun τ => 1 / (τ ^ 2 + (1 / 2) ^ 2) := by
      funext τ; ring
    rw [e, this]; ring
  set h : ℝ → ℝ → ℝ := fun c τ => Real.log (1 + (τ / c) ^ 2) / (1 / 4 + τ ^ 2) with hh
  have hbd : ∀ c : ℝ, 1 ≤ c → ∀ τ : ℝ,
      ‖h c τ‖ ≤ Real.log (τ ^ 2 + 9 / 4) / (1 / 4 + τ ^ 2) := by
    intro c hc τ
    have hw : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
    have hc0 : 0 < c := by linarith
    have h1 : (τ / c) ^ 2 ≤ τ ^ 2 := by
      rw [div_pow]
      apply div_le_self (sq_nonneg _)
      nlinarith
    have hl0 : 0 ≤ Real.log (1 + (τ / c) ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg (τ / c)])
    have hl1 : Real.log (1 + (τ / c) ^ 2) ≤ Real.log (τ ^ 2 + 9 / 4) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [hh, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hl0 hw.le)]
    exact div_le_div_of_nonneg_right hl1 hw.le
  have hmeas : ∀ c : ℝ, AEStronglyMeasurable (h c) volume := fun c =>
    Measurable.aestronglyMeasurable (by rw [hh]; fun_prop)
  have hint : ∀ c : ℝ, 1 ≤ c → Integrable (h c) := fun c hc =>
    dlw_integrable_log_weight.mono' (hmeas c) (Eventually.of_forall (hbd c hc))
  have hdom : Tendsto (fun c => ∫ τ, h c τ) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence
      (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) / (1 / 4 + τ ^ 2)) (F := h) (f := fun _ => (0 : ℝ))
      (l := atTop) (Eventually.of_forall hmeas)
      ((eventually_ge_atTop 1).mono fun c hc => Eventually.of_forall (hbd c hc))
      dlw_integrable_log_weight
      (Eventually.of_forall fun τ => by
        have ht : Tendsto (fun c : ℝ => τ / c) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h2 : Tendsto (fun c : ℝ => Real.log (1 + (τ / c) ^ 2) / (1 / 4 + τ ^ 2)) atTop
            (𝓝 (Real.log (1 + 0 ^ 2) / (1 / 4 + τ ^ 2))) := by
          refine Tendsto.div_const ?_ _
          refine (Real.continuousAt_log (by norm_num)).tendsto.comp ?_
          exact tendsto_const_nhds.add (ht.pow 2)
        simpa [hh] using h2)
    simpa using this
  have hlog : Tendsto (fun c : ℝ => 4 * π * (Real.log c - Real.log (1 / 2 + c))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun c : ℝ => 1 + 1 / 2 * c⁻¹) atTop (𝓝 (1 + 1 / 2 * 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul _)
    have h2 : Tendsto (fun c : ℝ => -(4 * π) * Real.log (1 + 1 / 2 * c⁻¹)) atTop
        (𝓝 (-(4 * π) * Real.log (1 + 1 / 2 * 0))) :=
      ((Real.continuousAt_log (by norm_num)).tendsto.comp h1).const_mul _
    simp only [mul_zero, add_zero, Real.log_one] at h2
    refine h2.congr' ((eventually_gt_atTop 0).mono fun c hc => ?_)
    have : 1 + 1 / 2 * c⁻¹ = (1 / 2 + c) / c := by field_simp; ring
    rw [this, Real.log_div (by positivity) hc.ne']
    ring
  have hsum := hdom.add hlog
  rw [add_zero] at hsum
  refine hsum.congr' ((eventually_ge_atTop 1).mono fun c hc => ?_)
  have hc0 : 0 < c := by linarith
  have hf : (fun τ : ℝ => Real.log (τ ^ 2 + c ^ 2) / (1 / 4 + τ ^ 2)) =
      fun τ => h c τ + (2 * Real.log c) * (1 / (1 / 4 + τ ^ 2)) := by
    funext τ
    have e : τ ^ 2 + c ^ 2 = c ^ 2 * (1 + (τ / c) ^ 2) := by field_simp; ring
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow, hh]
    push_cast
    ring
  simp only
  rw [hf, integral_add (hint c hc) (dlw_integrable_weight.const_mul _), integral_const_mul, hwI]
  ring

/-- P0014 page 35: exact statement of the parent leaf
`Prep1121VIIntegral.integral_log_weight`, from the three pieces above. -/
theorem integral_log_weight :
    ∫ τ : ℝ, Real.log (τ ^ 2 + 9 / 4) / (1 / 4 + τ ^ 2) = 4 * π * Real.log 2 := by
  set H : ℝ → ℝ := fun c => (∫ τ : ℝ, Real.log (τ ^ 2 + c ^ 2) / (1 / 4 + τ ^ 2)) -
      4 * π * Real.log (1 / 2 + c) with hH
  have hder : ∀ b : ℝ, 1 / 2 < b → HasDerivAt H 0 b := by
    intro b hb
    have h1 := hasDerivAt_param b (by linarith)
    rw [integral_partial_fraction b hb] at h1
    have hpos : 0 < 1 / 2 + b := by linarith
    have h2 : HasDerivAt (fun c : ℝ => 4 * π * Real.log (1 / 2 + c))
        (4 * π * (1 / (1 / 2 + b))) b := by
      have := ((Real.hasDerivAt_log hpos.ne').comp b
        ((hasDerivAt_id b).const_add (1 / 2))).const_mul (4 * π)
      simpa [one_div] using this
    convert h1.sub h2 using 1
    field_simp
    ring
  have hconst : ∀ B : ℝ, 3 / 2 ≤ B → H B = H (3 / 2) := by
    intro B hB
    have hcont : ContinuousOn H (Icc (3 / 2) B) := fun x hx =>
      (hder x (by linarith [hx.1])).continuousAt.continuousWithinAt
    have hd : ∀ x ∈ Ico (3 / 2) B, HasDerivWithinAt H 0 (Ici x) x := fun x hx =>
      (hder x (by linarith [hx.1])).hasDerivWithinAt
    exact constant_of_has_deriv_right_zero hcont hd B ⟨hB, le_rfl⟩
  have hH0 : H (3 / 2) = 0 := by
    have hc : Tendsto H atTop (𝓝 (H (3 / 2))) :=
      tendsto_const_nhds.congr'
        ((eventually_ge_atTop (3 / 2)).mono fun B hB => (hconst B hB).symm)
    exact tendsto_nhds_unique hc tendsto_param
  rw [hH] at hH0
  simp only at hH0
  have h9 : (3 / 2 : ℝ) ^ 2 = 9 / 4 := by norm_num
  have h2 : (1 / 2 : ℝ) + 3 / 2 = 2 := by norm_num
  rw [h9, h2] at hH0
  linarith

end LeanLab.HelfgottMajor.Prep1121DLogWeight

#print axioms LeanLab.HelfgottMajor.Prep1121DLogWeight.hasDerivAt_param
#print axioms LeanLab.HelfgottMajor.Prep1121DLogWeight.tendsto_param
#print axioms LeanLab.HelfgottMajor.Prep1121DLogWeight.integral_log_weight
