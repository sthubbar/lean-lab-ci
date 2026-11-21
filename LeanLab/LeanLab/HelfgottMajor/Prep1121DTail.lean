import LeanLab.HelfgottMajor.Prep1121DIntegrable

/-!
PREP 2026-11-21 deepening pass p2, route step `MainLemma41Split123.vertical_integral_bound`.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 35, the integral
after display 4.12, the tail above 10 of the certified integral. The parent leaf
`Prep1121VIIntegral.tail_le` is proved here with its exact statement from the pieces
below: the pointwise comparison with (2 log τ + 9/400)²/τ², an explicit antiderivative
G(τ) = -((L² + 4L + 8)/τ) with L = 2 log τ + 9/400, its limit 0 at infinity, and
log 10 ≤ 2.30291. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DTail
open Real MeasureTheory Set Filter Topology


/-- P0014 page 35, the tail of the integral after display 4.12: for τ ≥ 10,
log(τ² + 9/4) ≤ 2 log τ + 9/(4·100), since log(1 + x) ≤ x, and 1/(1/4 + τ²) ≤ 1/τ², so
log(τ² + 9/4)²/(1/4 + τ²) ≤ (2 log τ + 9/400)²/τ². -/
theorem tail_pointwise (τ : ℝ) (hτ : 10 ≤ τ) :
    Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤
      (2 * Real.log τ + 9 / 400) ^ 2 / τ ^ 2 := by
  have hτ0 : 0 < τ := by linarith
  have hx : 0 < τ ^ 2 + 9 / 4 := by positivity
  have hsplit : τ ^ 2 + 9 / 4 = τ ^ 2 * (1 + 9 / (4 * τ ^ 2)) := by field_simp
  have hl : Real.log (τ ^ 2 + 9 / 4) = 2 * Real.log τ + Real.log (1 + 9 / (4 * τ ^ 2)) := by
    rw [hsplit, Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have hsmall : 9 / (4 * τ ^ 2) ≤ 9 / 400 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hlog1 : Real.log (1 + 9 / (4 * τ ^ 2)) ≤ 9 / (4 * τ ^ 2) := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 9 / (4 * τ ^ 2) by positivity)
    linarith
  have hℓ0 : 0 ≤ Real.log (τ ^ 2 + 9 / 4) := Real.log_nonneg (by nlinarith)
  have hℓ : Real.log (τ ^ 2 + 9 / 4) ≤ 2 * Real.log τ + 9 / 400 := by linarith
  have hsq : Real.log (τ ^ 2 + 9 / 4) ^ 2 ≤ (2 * Real.log τ + 9 / 400) ^ 2 :=
    pow_le_pow_left₀ hℓ0 hℓ 2
  calc Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
      ≤ Real.log (τ ^ 2 + 9 / 4) ^ 2 / τ ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    _ ≤ (2 * Real.log τ + 9 / 400) ^ 2 / τ ^ 2 :=
        div_le_div_of_nonneg_right hsq (by positivity)

/-- P0014 page 35, the tail: G(τ) = -(((2 log τ + e)² + 4(2 log τ + e) + 8)/τ) has
derivative (2 log τ + e)²/τ² for τ > 0. -/
theorem tail_hasDerivAt (e τ : ℝ) (hτ : 0 < τ) :
    HasDerivAt (fun x : ℝ => -(((2 * Real.log x + e) ^ 2 + 4 * (2 * Real.log x + e) + 8) / x))
      ((2 * Real.log τ + e) ^ 2 / τ ^ 2) τ := by
  have hL : HasDerivAt (fun x : ℝ => 2 * Real.log x + e) (2 * τ⁻¹) τ := by
    simpa using ((Real.hasDerivAt_log hτ.ne').const_mul 2).add_const e
  have hN := ((hL.pow 2).add (hL.const_mul 4)).add_const 8
  have hQ := (hN.div (hasDerivAt_id τ) hτ.ne').neg
  convert hQ using 1
  · funext x
    simp only [Pi.neg_apply, Pi.div_apply, Pi.add_apply, Pi.pow_apply, id_eq]
  · simp only [id_eq]
    norm_num
    field_simp
    ring

/-- P0014 page 35, the tail of the integral after display 4.12: the antiderivative
G(τ) = -(((2 log τ + e)² + 4(2 log τ + e) + 8)/τ) tends to 0 as τ → ∞, because
log τ / τ and log² τ / τ tend to 0. PROVED here from Mathlib's
`Real.tendsto_pow_log_div_mul_add_atTop` with n = 0, 1, 2. -/
theorem tail_tendsto (e : ℝ) :
    Tendsto (fun x : ℝ => -(((2 * Real.log x + e) ^ 2 + 4 * (2 * Real.log x + e) + 8) / x))
      atTop (𝓝 0) := by
  have h2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h := (((h2.const_mul 4).add (h1.const_mul (4 * e + 8))).add
    (h0.const_mul (e ^ 2 + 4 * e + 8))).neg
  simp only [mul_zero, add_zero, neg_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [one_mul, pow_one, pow_zero]
  field_simp
  ring

/-- Numerical, log 10 ≤ 2.30291; the true value is 2.302585093, margin 3.2e-4.
Proof idea: log 10 = 3 log 2 + log(5/4), `Real.log_two_lt_d9`, and log(5/4) = -log(1 - 1/5)
≤ 1/5 + 1/50 + 1/375 + 1/2500 + (1/5)^5/(4/5) = 0.2234667 from
`Real.abs_log_sub_add_sum_range_le` with n = 4. PROVED here. -/
theorem log_ten_le : Real.log 10 ≤ 2.30291 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 5)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 4
  rw [show (1 : ℝ) - 1 / 5 = 2 ^ 3 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_pow] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_of_pos (show (0:ℝ) < 1 / 5 by norm_num)] at h
  have h2 := Real.log_two_lt_d9
  have := (abs_le.mp h).1
  norm_num at this
  linarith

/-- P0014 page 35, the integral after display 4.12, the tail above 10: exact statement of
the parent leaf `Prep1121VIIntegral.tail_le`. -/
theorem tail_le :
    ∫ τ in Ioi (10 : ℝ), Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 4.797 := by
  set G : ℝ → ℝ := fun x =>
    -(((2 * Real.log x + 9 / 400) ^ 2 + 4 * (2 * Real.log x + 9 / 400) + 8) / x) with hG
  have hcont : ContinuousWithinAt G (Ici 10) 10 :=
    (tail_hasDerivAt (9 / 400) 10 (by norm_num)).continuousAt.continuousWithinAt
  have hder : ∀ x ∈ Ioi (10 : ℝ), HasDerivAt G ((2 * Real.log x + 9 / 400) ^ 2 / x ^ 2) x :=
    fun x hx => tail_hasDerivAt (9 / 400) x (by linarith [mem_Ioi.mp hx])
  have hpos : ∀ x ∈ Ioi (10 : ℝ), 0 ≤ (2 * Real.log x + 9 / 400) ^ 2 / x ^ 2 :=
    fun x _ => by positivity
  have hlim := tail_tendsto (9 / 400)
  have hgi : IntegrableOn (fun x => (2 * Real.log x + 9 / 400) ^ 2 / x ^ 2) (Ioi 10) :=
    integrableOn_Ioi_deriv_of_nonneg hcont hder hpos hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg hcont hder hpos hlim
  have hfi : IntegrableOn (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2))
      (Ioi 10) := Prep1121DIntegrable.integrable_log_sq_weight.integrableOn
  have hmono := setIntegral_mono_on hfi hgi measurableSet_Ioi
    (fun τ hτ => tail_pointwise τ (le_of_lt (mem_Ioi.mp hτ)))
  refine hmono.trans ?_
  rw [hval, hG]
  simp only
  have h10 := log_ten_le
  have h10' : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  nlinarith

end LeanLab.HelfgottMajor.Prep1121DTail
