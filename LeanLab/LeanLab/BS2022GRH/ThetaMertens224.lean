/- AI wrote this Lean code for CODEX task224. Goldbach is open.
Abel summation for journal p. 1220 display 4.
Source: https://doi.org/10.1007/s11139-024-00866-x -/
import Mathlib

namespace LeanLab.BS2022GRH.ThetaMertens224
open Real Finset Filter MeasureTheory Topology
noncomputable section

/-- The signed theta error integrand in journal p. 1220 display 4. -/
def thetaError (t : ℝ) : ℝ :=
  (t - Chebyshev.theta t) * (1 + log t) / (t ^ 2 * log t ^ 2)

/-- The derivative of the reciprocal Abel weight. -/
theorem weight_derivative {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun y : ℝ => 1 / (y * log y))
      (-(1 + log t) / (t ^ 2 * log t ^ 2)) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hlog : log t ≠ 0 := ne_of_gt (log_pos ht)
  convert ((hasDerivAt_id t).mul (hasDerivAt_log ht0)).inv
    (mul_ne_zero ht0 hlog) using 1
  · ext y
    simp [one_div]
  · dsimp
    field_simp
    ring

/-- Finite Abel summation for prime reciprocals. -/
theorem reciprocal_abel {x : ℝ} (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) =
      Chebyshev.theta x / (x * log x) +
      ∫ t in 2..x, Chebyshev.theta t * (1 + log t) / (t ^ 2 * log t ^ 2) := by
  let c : ℕ → ℝ := fun n => if n.Prime then log n else 0
  have hsum (y : ℝ) : ∑ n ∈ Icc 0 ⌊y⌋₊, c n = Chebyshev.theta y := by
    simp [c, ← sum_filter, Chebyshev.theta_eq_sum_Icc]
  have hrecip : (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) =
      ∑ n ∈ Icc 0 ⌊x⌋₊, (1 / ((n : ℝ) * log n)) * c n := by
    rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · have hlog : log (n : ℝ) ≠ 0 := ne_of_gt (log_pos (by exact_mod_cast hp.one_lt))
      simp [c, hp]
      field_simp
    · simp [c, hp]
  rw [hrecip, sum_mul_eq_sub_integral_mul₁ c (f := fun t : ℝ => 1 / (t * log t)) (by simp [c]) (by simp [c]),
    hsum, ← intervalIntegral.integral_of_le hx]
  · rw [sub_eq_add_neg, ← intervalIntegral.integral_neg]
    congr 1
    · ring
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      dsimp only
      rw [(weight_derivative (t := t) (by linarith [ht.1])).deriv, hsum]
      ring
  · intro t ht
    exact (weight_derivative (by linarith [ht.1])).differentiableAt
  · apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.congr
      (f := fun t : ℝ => -(1 + log t) / (t ^ 2 * log t ^ 2))
    · intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hl0 : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
    · intro t ht
      exact (weight_derivative (by linarith [ht.1])).deriv

/-- Local integrability of the theta term in finite Abel summation. -/
theorem theta_weight_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t => Chebyshev.theta t * (1 + log t) / (t ^ 2 * log t ^ 2)) volume a b := by
  have hcont : ContinuousOn (fun t : ℝ => (1 + log t) / (t ^ 2 * log t ^ 2))
      (Set.Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one (ha.trans_le ht.1))
    have hl0 : log t ≠ 0 := ne_of_gt (log_pos (ha.trans_le ht.1))
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have h := integrableOn_mul_sum_Icc
    (fun n : ℕ => if n.Prime then log n else 0) (m := 0) (by linarith : 0 ≤ a)
    hcont.integrableOn_Icc
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  convert h using 1
  ext t
  simp only [← sum_filter, ← Chebyshev.theta_eq_sum_Icc]
  ring

/-- The elementary part of the Abel integrand is locally integrable above one. -/
theorem main_weight_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => t * (1 + log t) / (t ^ 2 * log t ^ 2)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one (ha.trans_le ht.1))
  have hl0 : log t ≠ 0 := ne_of_gt (log_pos (ha.trans_le ht.1))
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))

/-- The elementary part of the Abel integral. -/
theorem main_integral {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in 2..x, t * (1 + log t) / (t ^ 2 * log t ^ 2)) =
      log (log x) - log (log 2) + (log 2)⁻¹ - (log x)⁻¹ := by
  have h1 : IntervalIntegrable (fun t : ℝ => t⁻¹ / log t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := grind [Set.uIcc_of_le hx, log_pos, mul_ne_zero, pow_ne_zero])
  have h2 : IntervalIntegrable (fun t : ℝ => t⁻¹ / log t ^ 2) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := grind [Set.uIcc_of_le hx, log_pos, mul_ne_zero, pow_ne_zero])
  have heq : (∫ t in 2..x, t * (1 + log t) / (t ^ 2 * log t ^ 2)) =
      ∫ t in 2..x, (t⁻¹ / log t + t⁻¹ / log t ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
    field_simp
    ring
  rw [heq, intervalIntegral.integral_add h1 h2,
    integral_inv_div_log (by norm_num) (by linarith),
    integral_inv_div_log_sq (by norm_num) (by linarith)]
  ring

/-- The normalized finite form of journal display 4. -/
theorem normalized_abel {x : ℝ} (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) - log (log x) =
      (Chebyshev.theta x - x) / (x * log x) + (log 2)⁻¹ - log (log 2) -
      ∫ t in 2..x, thetaError t := by
  have hmain : IntervalIntegrable
      (fun t : ℝ => t * (1 + log t) / (t ^ 2 * log t ^ 2)) volume 2 x := by
    exact main_weight_integrable (by norm_num) hx
  have htheta := theta_weight_integrable (b := x) (by norm_num : (1 : ℝ) < 2) hx
  have heq : (∫ t in 2..x, thetaError t) =
      (∫ t in 2..x, t * (1 + log t) / (t ^ 2 * log t ^ 2)) -
      ∫ t in 2..x, Chebyshev.theta t * (1 + log t) / (t ^ 2 * log t ^ 2) := by
    rw [← intervalIntegral.integral_sub hmain htheta]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [thetaError]
    ring
  rw [heq, main_integral hx, reciprocal_abel hx]
  have hx0 : x ≠ 0 := by linarith
  have hl0 : log x ≠ 0 := ne_of_gt (log_pos (by linarith))
  field_simp
  ring

/-- The improper-integral identity follows from the common Mertens limit. -/
theorem reciprocal_tail (M : ℝ)
    (hlim : Tendsto (fun y : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p) - log (log y)) atTop (nhds M))
    {x : ℝ} (hx : 2 ≤ x)
    (hi : IntegrableOn thetaError (Set.Ioi x))
    (hb : Tendsto (fun y : ℝ => (Chebyshev.theta y - y) / (y * log y))
      atTop (nhds 0)) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) = log (log x) + M +
      (Chebyshev.theta x - x) / (x * log x) + ∫ t in Set.Ioi x, thetaError t := by
  have hnorm := normalized_abel hx
  have htail := intervalIntegral_tendsto_integral_Ioi x hi tendsto_id
  have hevent : (fun y : ℝ =>
      ((∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p) - log (log y)) -
      (Chebyshev.theta y - y) / (y * log y) + ∫ t in x..y, thetaError t)
      =ᶠ[atTop] (fun _ =>
        ((∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) - log (log x)) -
        (Chebyshev.theta x - x) / (x * log x)) := by
    filter_upwards [eventually_ge_atTop x] with y hy
    have hynorm := normalized_abel (hx.trans hy)
    have hlocal : IntervalIntegrable thetaError volume 2 y := by
      have hmain : IntervalIntegrable
          (fun t : ℝ => t * (1 + log t) / (t ^ 2 * log t ^ 2)) volume 2 y := by
        exact main_weight_integrable (by norm_num) (hx.trans hy)
      convert hmain.sub (theta_weight_integrable (b := y) (by norm_num : (1 : ℝ) < 2) (hx.trans hy)) using 1
      ext t
      dsimp [thetaError]
      ring
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hlocal.mono_set (by
        rw [Set.uIcc_of_le hx, Set.uIcc_of_le (hx.trans hy)]
        exact Set.Icc_subset_Icc le_rfl hy))
      (hlocal.mono_set (by
        rw [Set.uIcc_of_le hy, Set.uIcc_of_le (hx.trans hy)]
        exact Set.Icc_subset_Icc hx le_rfl))
    linarith
  have hconst := ((hlim.sub hb).add htail).congr' hevent
  have heq := tendsto_nhds_unique hconst tendsto_const_nhds
  linarith

/-- The positive majorant after a relative theta error of C over log t. -/
def kernel (t : ℝ) : ℝ := (1 + log t) / (t * log t ^ 3)

/-- An antiderivative of the majorant kernel. -/
def kernelPrimitive (t : ℝ) : ℝ := -(log t)⁻¹ - (1 / 2 : ℝ) * ((log t)⁻¹) ^ 2

/-- Differentiate the majorant used below display 4 on p. 1220. -/
theorem kernel_derivative {t : ℝ} (ht : 1 < t) :
    HasDerivAt kernelPrimitive (kernel t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hl0 : log t ≠ 0 := ne_of_gt (log_pos ht)
  convert ((hasDerivAt_log ht0).inv hl0).neg.sub
    ((((hasDerivAt_log ht0).inv hl0).pow 2).const_mul (1 / 2 : ℝ)) using 1
  · ext y
    dsimp [kernelPrimitive]
  · dsimp [kernel]
    field_simp
    ring

/-- The chosen primitive vanishes at infinity. -/
theorem kernelPrimitive_limit : Tendsto kernelPrimitive atTop (nhds 0) := by
  have h := tendsto_log_atTop.inv_tendsto_atTop
  change Tendsto (fun t : ℝ => -(log t)⁻¹ - (1 / 2 : ℝ) * ((log t)⁻¹) ^ 2) atTop (nhds 0)
  simpa using h.neg.sub ((h.pow 2).const_mul (1 / 2 : ℝ))

/-- The majorant is integrable on each tail above one. -/
theorem kernel_integrable {x : ℝ} (hx : 1 < x) :
    IntegrableOn kernel (Set.Ioi x) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (fun t ht => kernel_derivative (hx.trans_le ht))
    _ kernelPrimitive_limit
  intro t ht
  have ht0 : 0 < t := lt_trans zero_lt_one (hx.trans ht)
  have hl0 : 0 < log t := log_pos (hx.trans ht)
  dsimp [kernel]
  positivity

/-- Exact majorant tail integral for p. 1220. -/
theorem kernel_integral {x : ℝ} (hx : 1 < x) :
    (∫ t in Set.Ioi x, kernel t) = 1 / log x + 1 / (2 * log x ^ 2) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => kernel_derivative (hx.trans_le ht)) (kernel_integrable hx)
    kernelPrimitive_limit]
  simp only [kernelPrimitive]
  ring

/-- The theta error bound gives the integrable kernel majorant. -/
theorem thetaError_bound {C t : ℝ} (ht : 1 < t)
    (hθ : |Chebyshev.theta t - t| ≤ C * t / log t) :
    ‖thetaError t‖ ≤ C * kernel t := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hl0 : 0 < log t := log_pos ht
  rw [Real.norm_eq_abs, thetaError, abs_div, abs_mul, abs_sub_comm,
    abs_of_pos (by positivity : 0 < 1 + log t),
    abs_of_pos (by positivity : 0 < t ^ 2 * log t ^ 2)]
  calc
    _ ≤ (C * t / log t) * (1 + log t) / (t ^ 2 * log t ^ 2) := by gcongr
    _ = C * kernel t := by dsimp [kernel]; field_simp <;> ring

/-- Absolute integrability of the signed error follows from the explicit theta input. -/
theorem thetaError_integrable {C x : ℝ} (hx : 1 < x)
    (hθ : ∀ t : ℝ, x ≤ t → |Chebyshev.theta t - t| ≤ C * t / log t) :
    IntegrableOn thetaError (Set.Ioi x) := by
  apply ((kernel_integrable hx).const_mul C).mono'
  · have hmeas : Measurable Chebyshev.theta := by
      unfold Chebyshev.theta
      exact (measurable_from_top : Measurable
        (fun n : ℕ => ∑ p ∈ Ioc 0 n with p.Prime, log (p : ℝ))).comp Nat.measurable_floor
    exact (by unfold thetaError; fun_prop : Measurable thetaError).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact thetaError_bound (hx.trans ht) (hθ t ht.le)

/-- The theta endpoint error tends to zero under the explicit theta input. -/
theorem theta_boundary_limit {C x : ℝ}
    (hθ : ∀ t : ℝ, x ≤ t → |Chebyshev.theta t - t| ≤ C * t / log t) :
    Tendsto (fun t : ℝ => (Chebyshev.theta t - t) / (t * log t)) atTop (nhds 0) := by
  have hlim : Tendsto (fun t : ℝ => C * ((log t)⁻¹) ^ 2) atTop (nhds 0) := by
    simpa using (tendsto_log_atTop.inv_tendsto_atTop.pow 2).const_mul C
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (max x 2)] with t ht
  have ht2 : 2 ≤ t := (le_max_right x 2).trans ht
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < log t := log_pos (by linarith)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ht0 hl0)]
  calc
    _ ≤ (C * t / log t) / (t * log t) :=
      div_le_div_of_nonneg_right (hθ t ((le_max_left x 2).trans ht)) (by positivity)
    _ = C * ((log t)⁻¹) ^ 2 := by field_simp <;> ring

/-- Absolute value of the signed tail is bounded by the exact majorant integral. -/
theorem theta_tail_bound {C x : ℝ} (hx : 1 < x)
    (hθ : ∀ t : ℝ, x ≤ t → |Chebyshev.theta t - t| ≤ C * t / log t) :
    |∫ t in Set.Ioi x, thetaError t| ≤ C * (1 / log x + 1 / (2 * log x ^ 2)) := by
  calc
    _ ≤ ∫ t in Set.Ioi x, ‖thetaError t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi x, C * kernel t := by
      apply integral_mono_ae (thetaError_integrable hx hθ).norm ((kernel_integrable hx).const_mul C)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact thetaError_bound (hx.trans ht) (hθ t ht.le)
    _ = _ := by rw [integral_const_mul, kernel_integral hx]

/-- The explicit theta error controls the endpoint term in display 4. -/
theorem theta_endpoint_bound {C x : ℝ} (hx : 1 < x)
    (hθ : |Chebyshev.theta x - x| ≤ C * x / log x) :
    |(Chebyshev.theta x - x) / (x * log x)| ≤ C / log x ^ 2 := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hl0 : 0 < log x := log_pos hx
  rw [abs_div, abs_of_pos (mul_pos hx0 hl0)]
  calc
    _ ≤ (C * x / log x) / (x * log x) :=
      div_le_div_of_nonneg_right hθ (by positivity)
    _ = C / log x ^ 2 := by field_simp <;> ring

/-- The analytic upper estimate from a named explicit theta input. -/
theorem reciprocal_upper_from_theta (M C : ℝ)
    (hlim : Tendsto (fun y : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p) - log (log y)) atTop (nhds M))
    {x : ℝ} (hx : 2 ≤ x)
    (hθ : ∀ t : ℝ, x ≤ t → |Chebyshev.theta t - t| ≤ C * t / log t) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) ≤
      log (log x) + M + C / log x * (1 + 3 / (2 * log x)) := by
  have hx1 : 1 < x := by linarith
  rw [reciprocal_tail M hlim hx (thetaError_integrable hx1 hθ) (theta_boundary_limit hθ)]
  have hb := (le_abs_self _).trans (theta_endpoint_bound hx1 (hθ x le_rfl))
  have ht := (le_abs_self _).trans (theta_tail_bound hx1 hθ)
  have halg : C / log x ^ 2 + C * (1 / log x + 1 / (2 * log x ^ 2)) =
      C / log x * (1 + 3 / (2 * log x)) := by ring
  linarith

/-- The numerical rounding at log x equal to 2753 in journal display 3. -/
theorem upper_rounding {L : ℝ} (hL : 2753 ≤ L) :
    (2.2885e-9 : ℝ) * (1 + 3 / (2 * L)) ≤ 2.28975e-9 := by
  have hpos : 0 < 2 * L := by linarith
  have hfrac : (3 : ℝ) / (2 * L) ≤ 3 / (2 * 2753) := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  nlinarith

end
end LeanLab.BS2022GRH.ThetaMertens224

#print axioms LeanLab.BS2022GRH.ThetaMertens224.weight_derivative
#print axioms LeanLab.BS2022GRH.ThetaMertens224.reciprocal_abel
#print axioms LeanLab.BS2022GRH.ThetaMertens224.theta_weight_integrable
#print axioms LeanLab.BS2022GRH.ThetaMertens224.main_weight_integrable
#print axioms LeanLab.BS2022GRH.ThetaMertens224.main_integral
#print axioms LeanLab.BS2022GRH.ThetaMertens224.normalized_abel
#print axioms LeanLab.BS2022GRH.ThetaMertens224.reciprocal_tail
#print axioms LeanLab.BS2022GRH.ThetaMertens224.kernel_derivative
#print axioms LeanLab.BS2022GRH.ThetaMertens224.kernelPrimitive_limit
#print axioms LeanLab.BS2022GRH.ThetaMertens224.kernel_integrable
#print axioms LeanLab.BS2022GRH.ThetaMertens224.kernel_integral
#print axioms LeanLab.BS2022GRH.ThetaMertens224.thetaError_bound
#print axioms LeanLab.BS2022GRH.ThetaMertens224.thetaError_integrable
#print axioms LeanLab.BS2022GRH.ThetaMertens224.theta_boundary_limit
#print axioms LeanLab.BS2022GRH.ThetaMertens224.theta_tail_bound
#print axioms LeanLab.BS2022GRH.ThetaMertens224.theta_endpoint_bound
#print axioms LeanLab.BS2022GRH.ThetaMertens224.reciprocal_upper_from_theta
#print axioms LeanLab.BS2022GRH.ThetaMertens224.upper_rounding
