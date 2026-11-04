import LeanLab.ChenDoubleSieve.Decomp275f

/-!
The remaining logarithmic coefficient F9 in Wu 2004 Theorem 2.
Source: https://arxiv.org/pdf/0705.1652, page 41 equation 10.12 and page 42.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Task275.Thm2Scalar

/-- A rounded rational K cell for an arbitrary rational partition. -/
def roundedKCell (x : ℕ → ℚ) (r : ℚ) (j : ℕ) : ℚ :=
  Wu04JCertificate.up (Wu04KCertificate.upperPanelQ (x j) (x (j + 1)) r)

/-- The existing K panel theorem also applies to any admissible rational partition. -/
theorem K_rounded_partition (x : ℕ → ℚ) (r : ℚ) (m : ℕ) (hr : 0 < r)
    (hx : ∀ j < m, 0 < x j ∧ x j ≤ x (j + 1) ∧ x (j + 1) < 1 ∧ 1 ≤ r * x j - 1) :
    (∫ t in (x 0 : ℝ)..(x m : ℝ), log ((r : ℝ) * t - 1) / (t * (1 - t))) ≤
      ((∑ j ∈ range m, roundedKCell x r j : ℚ) : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hxR (j : ℕ) (hj : j < m) :
      (0 : ℝ) < x j ∧ (x j : ℝ) ≤ x (j + 1) ∧ (x (j + 1) : ℝ) < 1 ∧
        1 ≤ (r : ℝ) * x j - 1 := by exact_mod_cast hx j hj
  have hp := (Wu04Panels.K_partition_arithmetic 16 m (fun j => (x j : ℝ)) hrR hxR).2
  have hcell (j : ℕ) :
      Wu04Panels.KUpper 16 (x j) (x (j + 1)) r ≤ (roundedKCell x r j : ℝ) := by
    have h : (Wu04KCertificate.upperPanelQ (x j) (x (j + 1)) r : ℝ) ≤
        (roundedKCell x r j : ℝ) := by
      exact_mod_cast Wu04JCertificate.le_up (Wu04KCertificate.upperPanelQ (x j) (x (j + 1)) r)
    simpa [roundedKCell, Wu04KCertificate.upperPanelQ, Wu04KCertificate.wLowerQ,
      Wu04KCertificate.wUpperQ, Wu04Panels.KUpper, Wu04Panels.KWLower,
      Wu04Panels.KWUpper] using h
  exact hp.trans (by simpa only [Rat.cast_sum] using
    (sum_le_sum (fun j (_ : j ∈ range m) => hcell j)))

/-- An antiderivative for the reciprocal square part after reflecting the early F9 interval. -/
def squarePrimitive (r u : ℝ) : ℝ := -log (r * u - 1) / u + r * log ((r * u - 1) / u)

/-- The antiderivative follows by differentiating logarithms and rational functions. -/
theorem squarePrimitive_deriv (r u : ℝ) (hu : 0 < u) (hra : 0 < r * u - 1) :
    HasDerivAt (squarePrimitive r) (log (r * u - 1) / u ^ 2) u := by
  have hg := ((hasDerivAt_id u).const_mul r).sub_const 1
  have hl := hg.log hra.ne'
  have hq := hg.div (hasDerivAt_id u) hu.ne'
  have hd := (hl.neg.div (hasDerivAt_id u) hu.ne').add
    ((hq.log (div_ne_zero hra.ne' hu.ne')).const_mul r)
  convert hd using 1
  · rfl
  · dsimp
    field_simp [hu.ne', hra.ne']
    ring

/-- The reciprocal square logarithmic integrand is integrable on a positive compact interval. -/
theorem square_integrable {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : 0 < r) (hra : 0 < r * a - 1) :
    IntervalIntegrable (fun u => log (r * u - 1) / u ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply ContinuousOn.log (by fun_prop)
    intro u hu
    exact ne_of_gt (by nlinarith [hu.1] : 0 < r * u - 1)
  · fun_prop
  · intro u hu
    exact pow_ne_zero 2 (ha.trans_le hu.1).ne'

/-- Exact evaluation of that reciprocal square integral. -/
theorem square_integral_eq {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : 0 < r) (hra : 0 < r * a - 1) :
    (∫ u in a..b, log (r * u - 1) / u ^ 2) = squarePrimitive r b - squarePrimitive r a := by
  exact integral_eq_sub_of_hasDerivAt
    (fun u hu => by
      rw [uIcc_of_le hab] at hu
      exact squarePrimitive_deriv r u (ha.trans_le hu.1) (by nlinarith [hu.1]))
    (square_integrable ha hab hr hra)

/-- A rational upper evaluation of the reciprocal square integral at the F9 endpoints. -/
def squareUpperQ : ℚ :=
  let a : ℚ := 9 / 10
  let b : ℚ := 11 / 12
  let r : ℚ := 125 / 41
  Wu04Integral.logUpperQ 16 (r * a - 1) / a -
    Wu04Integral.logLowerQ 16 (r * b - 1) / b +
    r * (Wu04Integral.logUpperQ 16 ((r * b - 1) / b) -
      Wu04Integral.logLowerQ 16 ((r * a - 1) / a))

/-- The actual reciprocal square part lies below that rational expression. -/
theorem square_upper :
    (∫ u in (9 / 10 : ℝ)..(11 / 12 : ℝ),
      log ((125 / 41 : ℝ) * u - 1) / u ^ 2) ≤ (squareUpperQ : ℝ) := by
  have he := square_integral_eq (a := (9 / 10 : ℝ)) (b := 11 / 12)
    (r := 125 / 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := (Wu04Integral.log_bounds 16 (y := (125 / 41 : ℝ) * (9 / 10) - 1) (by norm_num)).2
  have h2 := (Wu04Integral.log_bounds 16 (y := (125 / 41 : ℝ) * (11 / 12) - 1) (by norm_num)).1
  have h3 := (Wu04Integral.log_bounds 16
    (y := ((125 / 41 : ℝ) * (11 / 12) - 1) / (11 / 12)) (by norm_num)).2
  have h4 := (Wu04Integral.log_bounds 16
    (y := ((125 / 41 : ℝ) * (9 / 10) - 1) / (9 / 10)) (by norm_num)).1
  have hc : (squareUpperQ : ℝ) =
      Wu04Integral.logUpper 16 ((125 / 41 : ℝ) * (9 / 10) - 1) / (9 / 10) -
        Wu04Integral.logLower 16 ((125 / 41 : ℝ) * (11 / 12) - 1) / (11 / 12) +
        (125 / 41) * (Wu04Integral.logUpper 16 (((125 / 41 : ℝ) * (11 / 12) - 1) / (11 / 12)) -
          Wu04Integral.logLower 16 (((125 / 41 : ℝ) * (9 / 10) - 1) / (9 / 10))) := by
    simp [squareUpperQ]
  rw [he, hc]
  dsimp only [squarePrimitive]
  norm_num at h1 h2 h3 h4 ⊢
  linarith

/-- The reflected first interval in F9, with 32 panels. -/
def earlyNodeQ (j : ℕ) : ℚ := 9 / 10 + j * (11 / 12 - 9 / 10) / 32
/-- The reflected second interval in F9, with 1024 panels. -/
def lateNodeQ (j : ℕ) : ℚ := 84 / 125 + j * (9 / 10 - 84 / 125) / 1024

/-- Both rational partitions satisfy the existing K panel hypotheses. -/
theorem F9_partition_parameters :
    (∀ j ∈ range 32, 0 < earlyNodeQ j ∧ earlyNodeQ j ≤ earlyNodeQ (j + 1) ∧
      earlyNodeQ (j + 1) < 1 ∧ 1 ≤ (125 / 41 : ℚ) * earlyNodeQ j - 1) ∧
    (∀ j ∈ range 1024, 0 < lateNodeQ j ∧ lateNodeQ j ≤ lateNodeQ (j + 1) ∧
      lateNodeQ (j + 1) < 1 ∧ 1 ≤ (125 / 41 : ℚ) * lateNodeQ j - 1) := by
  decide +kernel

/-- An exact rational certificate for the complete printed F9 upper bound. -/
theorem F9_certificate :
    (36 / 5 : ℚ) * ((∑ j ∈ range 32, roundedKCell earlyNodeQ (125 / 41) j) + squareUpperQ) +
      8 * (∑ j ∈ range 1024, roundedKCell lateNodeQ (125 / 41) j) ≤ 5161945 / 1000000 := by
  decide +kernel

/-- Reflection splits the early F9 integral into its K and reciprocal square parts. -/
theorem F9_early_substitution :
    (∫ t in kappa1..(1 / 10 : ℝ),
      log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t) ^ 2)) =
      (∫ u in (9 / 10 : ℝ)..(11 / 12 : ℝ),
        log ((125 / 41 : ℝ) * u - 1) / (u * (1 - u))) +
      ∫ u in (9 / 10 : ℝ)..(11 / 12 : ℝ), log ((125 / 41 : ℝ) * u - 1) / u ^ 2 := by
  let g := fun u : ℝ => log ((125 / 41 : ℝ) * u - 1) / (u * (1 - u)) +
    log ((125 / 41 : ℝ) * u - 1) / u ^ 2
  have hlog (t : ℝ) : 1 / sigma1 - 1 - t / sigma1 = (125 / 41 : ℝ) * (1 - t) - 1 := by
    norm_num [sigma1]
    ring
  calc
    _ = ∫ t in kappa1..(1 / 10 : ℝ), g (1 - t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num [kappa1] : kappa1 ≤ (1 / 10 : ℝ))] at ht
      have ht0 : t ≠ 0 := by have := ht.1; norm_num [kappa1] at this; linarith
      have ht1 : 1 - t ≠ 0 := by linarith [ht.2]
      dsimp [g]
      rw [hlog t]
      have he : 1 - (1 - t) = t := by ring
      rw [he]
      field_simp [ht0, ht1]
      ring
    _ = ∫ u in (1 - (1 / 10 : ℝ))..(1 - kappa1), g u := integral_comp_sub_left g 1
    _ = ∫ u in (9 / 10 : ℝ)..(11 / 12 : ℝ), g u := by norm_num [kappa1]
    _ = _ := integral_add
      (Wu04Panels.K_integrable (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (square_integrable (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- Reflection transforms the second F9 integral into its K form. -/
theorem F9_late_substitution :
    (∫ t in (1 / 10 : ℝ)..sigma1,
      log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t))) =
      ∫ u in (84 / 125 : ℝ)..(9 / 10 : ℝ),
        log ((125 / 41 : ℝ) * u - 1) / (u * (1 - u)) := by
  have hlog (t : ℝ) : 1 / sigma1 - 1 - t / sigma1 = (125 / 41 : ℝ) * (1 - t) - 1 := by
    norm_num [sigma1]
    ring
  calc
    _ = ∫ t in (1 / 10 : ℝ)..sigma1,
        (fun u : ℝ => log ((125 / 41 : ℝ) * u - 1) / (u * (1 - u))) (1 - t) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp
      rw [hlog t]
      congr 1
      ring
    _ = ∫ u in (1 - sigma1)..(1 - (1 / 10 : ℝ)),
        log ((125 / 41 : ℝ) * u - 1) / (u * (1 - u)) :=
      integral_comp_sub_left
        (fun u : ℝ => log ((125 / 41 : ℝ) * u - 1) / (u * (1 - u))) 1
    _ = _ := by norm_num [sigma1]

/-- The actual F9 coefficient satisfies the printed upper bound without an analytic input. -/
theorem F9_upper (F f ω : ℝ → ℝ) : integralTerms F f ω 8 ≤ 5.161945 := by
  have he := K_rounded_partition earlyNodeQ (125 / 41) 32 (by norm_num)
    (fun j hj => F9_partition_parameters.1 j (mem_range.mpr hj))
  have hl := K_rounded_partition lateNodeQ (125 / 41) 1024 (by norm_num)
    (fun j hj => F9_partition_parameters.2 j (mem_range.mpr hj))
  norm_num [earlyNodeQ] at he
  norm_num [lateNodeQ] at hl
  have hc : (36 / 5 : ℝ) *
      (((∑ j ∈ range 32, roundedKCell earlyNodeQ (125 / 41) j : ℚ) : ℝ) + (squareUpperQ : ℝ)) +
      8 * ((∑ j ∈ range 1024, roundedKCell lateNodeQ (125 / 41) j : ℚ) : ℝ) ≤ 5.161945 := by
    have hq := (Rat.cast_le (K := ℝ)).mpr F9_certificate
    convert hq using 1 <;> push_cast <;> norm_num
  push_cast at hc
  change (36 / 5 : ℝ) * (∫ t in kappa1..(1 / 10 : ℝ),
    log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t) ^ 2)) +
      8 * (∫ t in (1 / 10 : ℝ)..sigma1,
        log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t))) ≤ 5.161945
  rw [F9_early_substitution, F9_late_substitution]
  linarith [square_upper]

end LeanLab.ChenDoubleSieve.Task275.Thm2Scalar
