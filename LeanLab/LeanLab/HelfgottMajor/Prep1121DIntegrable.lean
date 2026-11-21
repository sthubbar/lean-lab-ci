import LeanLab.HelfgottMajor.Prep1121VIIntegral
import LeanLab.HelfgottMajor.Prep1121VIBudget

/-!
PREP 2026-11-21 deepening pass p2, route step `MainLemma41Split123.vertical_integral_bound`.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 35, the integral
after display 4.12. The three parent leaves `Prep1121VIIntegral.expand_square`,
`Prep1121VIIntegral.half_line_split` and `Prep1121VIBudget.memLp_split` all rest on one
fact: with ℓ = log(τ² + 9/4) and w = 1/(1/4 + τ²), the functions w, ℓ w and ℓ² w are
integrable on ℝ. Here that fact is reduced to the pointwise bound `log_sq_weight_le`,
a comparison with (1 + |τ|)^(-3/2), proved here, and the three parents are proved with their exact
statements, with no sorry in this file. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DIntegrable
open Real MeasureTheory Set

/-- P0014 page 35, the integral after display 4.12, implicit in the paper's numerical
evaluation over ℝ: ℓ² w = O(|τ|^(-3/2)), precisely
log(τ² + 9/4)² / (1/4 + τ²) ≤ 1000 (1 + |τ|)^(-3/2) for all real τ. Proof idea: log x ≤
8 x^(1/8) for x ≥ 1, so ℓ² ≤ 64 (τ² + 9/4)^(1/4) ≤ 64 (3/2)^(1/2) (1 + |τ|)^(1/2), and
(1 + |τ|)² ≤ 8 (1/4 + τ²); the constant needed is about 627.
PROVED here with c = (1 + |τ|)^(1/8), log(τ² + 9/4) ≤
16c - 14.75 and the polynomial inequality (16c - 14.75)² ≤ 125 c⁴ for c ≥ 1. -/
theorem log_sq_weight_le (τ : ℝ) :
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

/-- w = 1/(1/4 + τ²) is integrable on ℝ, from `integrable_inv_one_add_sq`. -/
theorem integrable_weight : Integrable (fun τ : ℝ => 1 / (1 / 4 + τ ^ 2)) := by
  have h : (fun τ : ℝ => 1 / (1 / 4 + τ ^ 2)) = fun τ => 4 * (1 + (2 * τ) ^ 2)⁻¹ := by
    funext τ
    have : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
    have : (0 : ℝ) < 1 + (2 * τ) ^ 2 := by positivity
    field_simp
    ring
  rw [h]
  exact ((integrable_inv_one_add_sq).comp_mul_left' (two_ne_zero)).const_mul 4

/-- ℓ² w is integrable on ℝ, from the leaf `log_sq_weight_le` and
`integrable_one_add_norm`. -/
theorem integrable_log_sq_weight :
    Integrable (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) := by
  have hI : Integrable (fun τ : ℝ => (1 + ‖τ‖) ^ (-(3 / 2 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  refine (hI.const_mul 1000).mono' (Measurable.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact log_sq_weight_le τ

/-- ℓ w is integrable on ℝ: |ℓ| ≤ 1 + ℓ², so |ℓ w| ≤ w + ℓ² w. -/
theorem integrable_log_weight :
    Integrable (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) / (1 / 4 + τ ^ 2)) := by
  refine (integrable_weight.add integrable_log_sq_weight).mono'
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

/-- P0014 page 35, exact statement of the parent leaf `Prep1121VIIntegral.expand_square`. -/
theorem expand_square (C : ℝ) :
    ∫ τ : ℝ, ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + C) ^ 2 / (1 / 4 + τ ^ 2) =
      (1 / 4) * (∫ τ : ℝ, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
        C * (∫ τ : ℝ, Real.log (τ ^ 2 + 9 / 4) / (1 / 4 + τ ^ 2)) +
        C ^ 2 * (∫ τ : ℝ, 1 / (1 / 4 + τ ^ 2)) := by
  have h : (fun τ : ℝ => ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + C) ^ 2 / (1 / 4 + τ ^ 2)) =
      fun τ => ((1 / 4) * (Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
        C * (Real.log (τ ^ 2 + 9 / 4) / (1 / 4 + τ ^ 2))) +
        C ^ 2 * (1 / (1 / 4 + τ ^ 2)) := by
    funext τ; ring
  rw [h, integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
  · exact integrable_log_sq_weight.const_mul _
  · exact integrable_log_weight.const_mul _
  · exact (integrable_log_sq_weight.const_mul _).add (integrable_log_weight.const_mul _)
  · exact integrable_weight.const_mul _

/-- P0014 page 35, exact statement of the parent leaf `Prep1121VIBudget.memLp_split`. -/
theorem memLp_split (A K : ℝ) :
    MemLp (fun τ : ℝ => A / Real.sqrt (1 / 4 + τ ^ 2)) 2 ∧
      MemLp (fun τ : ℝ => ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + K) /
        Real.sqrt (1 / 4 + τ ^ 2)) 2 := by
  have hsq : ∀ τ : ℝ, Real.sqrt (1 / 4 + τ ^ 2) ^ 2 = 1 / 4 + τ ^ 2 := fun τ =>
    Real.sq_sqrt (by positivity)
  constructor
  · rw [memLp_two_iff_integrable_sq (Measurable.aestronglyMeasurable (by fun_prop))]
    have h : (fun τ : ℝ => (A / Real.sqrt (1 / 4 + τ ^ 2)) ^ 2) =
        fun τ => A ^ 2 * (1 / (1 / 4 + τ ^ 2)) := by
      funext τ; rw [div_pow, hsq]; ring
    rw [h]; exact integrable_weight.const_mul _
  · rw [memLp_two_iff_integrable_sq (Measurable.aestronglyMeasurable (by fun_prop))]
    have h : (fun τ : ℝ => (((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + K) /
        Real.sqrt (1 / 4 + τ ^ 2)) ^ 2) =
        fun τ => ((1 / 4) * (Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
          K * (Real.log (τ ^ 2 + 9 / 4) / (1 / 4 + τ ^ 2))) +
          K ^ 2 * (1 / (1 / 4 + τ ^ 2)) := by
      funext τ; rw [div_pow, hsq]; ring
    rw [h]
    exact ((integrable_log_sq_weight.const_mul _).add (integrable_log_weight.const_mul _)).add
      (integrable_weight.const_mul _)

/-- P0014 page 35, exact statement of the parent leaf `Prep1121VIIntegral.half_line_split`. -/
theorem half_line_split :
    ∫ τ in Ioi (0 : ℝ), Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) =
      ((∫ τ in (0 : ℝ)..0.14, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.14 : ℝ)..0.28, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.28 : ℝ)..0.29, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.29 : ℝ)..0.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.45 : ℝ)..0.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.65 : ℝ)..0.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.9 : ℝ)..1.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2))) +
      ((∫ τ in (1.2 : ℝ)..1.6, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (1.6 : ℝ)..2.1, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (2.1 : ℝ)..2.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (2.8 : ℝ)..3.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (3.8 : ℝ)..5.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (5.2 : ℝ)..7.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (7.2 : ℝ)..10, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2))) +
      ∫ τ in Ioi (10 : ℝ), Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) := by
  set f : ℝ → ℝ := fun τ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) with hf
  have hint : Integrable f := integrable_log_sq_weight
  have hi : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hint.intervalIntegrable
  have hadd : ∀ a b c : ℝ, ∫ τ in a..c, f τ = (∫ τ in a..b, f τ) + ∫ τ in b..c, f τ :=
    fun a b c => (intervalIntegral.integral_add_adjacent_intervals (hi a b) (hi b c)).symm
  have hIoi : ∫ τ in Ioi (0 : ℝ), f τ = (∫ τ in (0 : ℝ)..10, f τ) + ∫ τ in Ioi (10 : ℝ), f τ :=
    (intervalIntegral.integral_interval_add_Ioi hint.integrableOn hint.integrableOn).symm
  rw [hIoi]
  have e1 := hadd 0 0.14 10
  have e2 := hadd 0.14 0.28 10
  have e3 := hadd 0.28 0.29 10
  have e4 := hadd 0.29 0.45 10
  have e5 := hadd 0.45 0.65 10
  have e6 := hadd 0.65 0.9 10
  have e7 := hadd 0.9 1.2 10
  have e8 := hadd 1.2 1.6 10
  have e9 := hadd 1.6 2.1 10
  have e10 := hadd 2.1 2.8 10
  have e11 := hadd 2.8 3.8 10
  have e12 := hadd 3.8 5.2 10
  have e13 := hadd 5.2 7.2 10
  linarith

end LeanLab.HelfgottMajor.Prep1121DIntegrable
