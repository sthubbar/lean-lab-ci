import LeanLab.HelfgottMajor.Prep1121VIIntegral
import LeanLab.HelfgottMajor.Prep1121DIntegrable

/-!
PREP 2026-11-21 deepening pass p2, route step `MainLemma41Split123.vertical_integral_bound`.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 35, the exact part
of the integral after display 4.12: ∫_ℝ log(τ² + 9/4)/(1/4 + τ²) dτ = 4π log 2. The paper
evaluates the whole integral numerically; the lab route needs this closed form. The parent
leaf `Prep1121VIIntegral.integral_log_weight` is proved here with its exact statement by
differentiation in the parameter b of G(b) = ∫ log(τ² + b²)/(1/4 + τ²) dτ: G'(b) = 4π/(1/2 + b)
for b above 1/2 by partial fractions, so G(b) - 4π log(1/2 + b) is constant on [3/2, ∞), and
it tends to 0 at infinity, so it vanishes at b = 3/2. Two LEAF pieces remain.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DLogWeight
open Real MeasureTheory Set Filter Topology

/-- The logarithmically weighted reciprocal quadratic is integrable for every positive
parameter.  This is the uniform-input analogue of `Prep1121DIntegrable.integrable_log_weight`. -/
theorem integrable_log_weight_general (c : ℝ) (hc : 0 < c) :
    Integrable (fun τ : ℝ => Real.log (τ ^ 2 + c ^ 2) / (1 / 4 + τ ^ 2)) := by
  let A : ℝ := |2 * Real.log c|
  let K : ℝ := Real.log (1 + c ^ 2)
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hK : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by nlinarith)
  have hlower : ∀ τ : ℝ, 2 * Real.log c ≤ Real.log (τ ^ 2 + c ^ 2) := by
    intro τ
    have hp : 0 < τ ^ 2 + c ^ 2 := by positivity
    have hc2pos : 0 < c ^ 2 := hc2
    have := Real.log_le_log (by positivity : 0 < c ^ 2) hp
    rw [Real.log_pow] at this
    simpa [Real.log_pow] using this
  have hupper : ∀ τ : ℝ,
      Real.log (τ ^ 2 + c ^ 2) ≤ Real.log (τ ^ 2 + 9 / 4) + K := by
    intro τ
    have hprod : τ ^ 2 + c ^ 2 ≤ (τ ^ 2 + 1) * (1 + c ^ 2) := by
      nlinarith [sq_nonneg τ]
    have hp : 0 < τ ^ 2 + c ^ 2 := by positivity
    have hq : 0 < (τ ^ 2 + 1) * (1 + c ^ 2) := by positivity
    have hlog := Real.log_le_log hp hq hprod
    rw [Real.log_mul (by positivity : 0 < τ ^ 2 + 1) (by positivity : 0 < 1 + c ^ 2)] at hlog
    dsimp [K]
    exact hlog
  have hL : ∀ τ : ℝ, 0 ≤ Real.log (τ ^ 2 + 9 / 4) := by
    intro τ
    exact Real.log_nonneg (by nlinarith [sq_nonneg τ])
  have hbound : ∀ τ : ℝ,
      |Real.log (τ ^ 2 + c ^ 2)| ≤ A + K + Real.log (τ ^ 2 + 9 / 4) := by
    intro τ
    have habs := abs_le_max_abs_abs (hlower τ) (hupper τ)
    have hmax : max |2 * Real.log c| |Real.log (τ ^ 2 + 9 / 4) + K| ≤
        A + K + Real.log (τ ^ 2 + 9 / 4) := by
      apply max_le
      · exact le_abs_self (2 * Real.log c)
      · rw [abs_of_nonneg (by linarith [hL τ, hK])]
        dsimp [A, K]
        linarith [abs_nonneg (2 * Real.log c)]
    simpa [A, K, abs_of_nonneg (by linarith [hL τ, hK])] using habs.trans hmax
  have hg : Integrable (fun τ : ℝ =>
      (A + K) * (1 / (1 / 4 + τ ^ 2)) +
        Real.log (τ ^ 2 + 9 / 4) * (1 / (1 / 4 + τ ^ 2))) := by
    exact (LeanLab.HelfgottMajor.Prep1121DIntegrable.integrable_weight.const_mul (A + K)).add
      LeanLab.HelfgottMajor.Prep1121DIntegrable.integrable_log_weight
  refine hg.mono (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [] with τ
  have hw : 0 < 1 / 4 + τ ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hw]
  apply (div_le_div_iff₀ hw (by positivity)).2
  have hnum := hbound τ
  dsimp [A, K] at hnum ⊢
  linarith

/-- LEAF: P0014 page 35, the exact part of the integral after display 4.12, step one:
differentiation under the integral sign in b, for b > 0,
d/db ∫ log(τ² + b²)/(1/4 + τ²) dτ = ∫ 2b/((τ² + b²)(1/4 + τ²)) dτ.
Class MEDIUM: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on a ball around b inside
(b/2, 2b), with the dominating function (4/b)/(1/4 + τ²) and integrability of
log(τ² + c²)/(1/4 + τ²), as in `Prep1121DIntegrable`. -/
theorem hasDerivAt_param (b : ℝ) (hb : 0 < b) :
    HasDerivAt (fun c : ℝ => ∫ τ : ℝ, Real.log (τ ^ 2 + c ^ 2) / (1 / 4 + τ ^ 2))
      (∫ τ : ℝ, 2 * b / ((τ ^ 2 + b ^ 2) * (1 / 4 + τ ^ 2))) b := by
  let s : Set ℝ := Ioo (b / 2) (2 * b)
  have hs : s ∈ 𝓝 b := by
    dsimp [s]
    exact Ioo_mem_nhds (by linarith) (by linarith)
  let F : ℝ → ℝ → ℝ := fun c τ =>
    Real.log (τ ^ 2 + c ^ 2) / (1 / 4 + τ ^ 2)
  let F' : ℝ → ℝ → ℝ := fun c τ =>
    2 * c / ((τ ^ 2 + c ^ 2) * (1 / 4 + τ ^ 2))
  have hF_meas : ∀ᶠ c in 𝓝 b, AEStronglyMeasurable (F c) := by
    filter_upwards [] with c
    exact (Measurable.aestronglyMeasurable (by fun_prop))
  have hF_int : Integrable (F b) := by
    exact integrable_log_weight_general b hb
  have hF'_meas : AEStronglyMeasurable (F' b) := by
    exact Measurable.aestronglyMeasurable (by fun_prop)
  have h_bound : ∀ᵐ τ ∂volume, ∀ c ∈ s,
      ‖F' c τ‖ ≤ (4 / b) / (1 / 4 + τ ^ 2) := by
    filter_upwards [] with τ
    intro c hc
    have hc' : b / 2 < c := (hc.1 : b / 2 < c)
    have hc0 : 0 < c := by linarith
    have hτ : 0 < τ ^ 2 + c ^ 2 := by positivity
    have hw : 0 < 1 / 4 + τ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * c)]
    apply (div_le_div_iff₀ hw (by positivity : 0 < 4 / b)).2
    have hsq : 0 ≤ τ ^ 2 := sq_nonneg τ
    nlinarith
  have hbound_int : Integrable (fun τ : ℝ => (4 / b) / (1 / 4 + τ ^ 2)) := by
    exact LeanLab.HelfgottMajor.Prep1121DIntegrable.integrable_weight.const_mul (4 / b)
  have h_diff : ∀ᵐ τ ∂volume, ∀ c ∈ s, HasDerivAt (F · τ) (F' c τ) c := by
    filter_upwards [] with τ
    intro c hc
    have hc' : b / 2 < c := (hc.1 : b / 2 < c)
    have hc0 : 0 < c := by linarith
    have hτ : 0 < τ ^ 2 + c ^ 2 := by positivity
    have hpoly : HasDerivAt (fun t : ℝ => t ^ 2 + τ ^ 2) (2 * c) c := by
      simpa using ((hasDerivAt_id c).pow 2).const_add (τ ^ 2)
    have hlog := (Real.hasDerivAt_log hτ.ne').comp c hpoly
    have hdiv := hlog.div_const (1 / 4 + τ ^ 2)
    simpa [F, F', div_eq_mul_inv] using hdiv
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := s) (x₀ := b) (F := F) (F' := F')
    (bound := fun τ : ℝ => (4 / b) / (1 / 4 + τ ^ 2))
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact hresult.2

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

/-- LEAF: P0014 page 35, the exact part of the integral after display 4.12, step three:
∫ log(τ² + c²)/(1/4 + τ²) dτ - 4π log(1/2 + c) tends to 0 as c → ∞. Writing
log(τ² + c²) = 2 log c + log(1 + τ²/c²) and ∫ 1/(1/4 + τ²) = 2π, the difference is
∫ log(1 + τ²/c²)/(1/4 + τ²) dτ + 4π (log c - log(1/2 + c)); the first term tends to 0 by
dominated convergence with the bound log(1 + τ²)/(1/4 + τ²) for c ≥ 1, the second by
continuity of log at 1. Class MEDIUM: `tendsto_integral_filter_of_dominated_convergence`. -/
theorem tendsto_param :
    Tendsto (fun c : ℝ => (∫ τ : ℝ, Real.log (τ ^ 2 + c ^ 2) / (1 / 4 + τ ^ 2)) -
      4 * π * Real.log (1 / 2 + c)) atTop (𝓝 0) := by
  sorry

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
