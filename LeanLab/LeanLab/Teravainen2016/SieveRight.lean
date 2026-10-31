/-
P0076 Definition 6.3 and the page 47 numerical margin.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.SieveTangent

open MeasureTheory intervalIntegral Set

namespace LeanLab.Teravainen2016

noncomputable def sieveEndpoint : ℝ := Real.sqrt (23 / 60)

theorem sieveEndpoint_bounds : (11 : ℝ) / 20 < sieveEndpoint ∧ sieveEndpoint < 31 / 50 := by
  unfold sieveEndpoint
  constructor
  · exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  · exact (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Monotone substitution removes the square root singularity on the right. -/
theorem sieve_right_substitution :
    (20 / 19 : ℝ) * (∫ t in (2 : ℝ)..(120 / 37),
      Real.log (t - 1) / (t * Real.sqrt (1 - t / (120 / 37)))) =
      (40 / 19 : ℝ) * ∫ u in (0 : ℝ)..sieveEndpoint, sieveRightIntegrand u := by
  have ha := sieveEndpoint_bounds
  have ha0 : 0 < sieveEndpoint := by linarith
  have ha2 : sieveEndpoint ^ 2 = 23 / 60 := Real.sq_sqrt (by norm_num)
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => (120 / 37) * (1 - u ^ 2))
      (-(2 * (120 / 37) * u)) u := by
    intro u
    convert (((hasDerivAt_const u 1).sub ((hasDerivAt_id u).pow 2)).const_mul (120 / 37)) using 1
    · rfl
    · simp
      ring
  have hsub := integral_comp_mul_deriv_of_deriv_nonpos
    (a := 0) (b := sieveEndpoint) (f := fun u : ℝ => (120 / 37) * (1 - u ^ 2))
    (f' := fun u => -(2 * (120 / 37) * u))
    (g := fun t : ℝ => Real.log (t - 1) / (t * Real.sqrt (1 - t / (120 / 37))))
    (by fun_prop) (fun u _ => hd u) (by
      intro u hu
      rw [min_eq_left ha0.le, max_eq_right ha0.le] at hu
      linarith [hu.1])
  have he : (∫ u in (0 : ℝ)..sieveEndpoint,
      ((fun t : ℝ => Real.log (t - 1) / (t * Real.sqrt (1 - t / (120 / 37)))) ∘
        (fun u : ℝ => (120 / 37) * (1 - u ^ 2))) u * (-(2 * (120 / 37) * u))) =
      -2 * ∫ u in (0 : ℝ)..sieveEndpoint, sieveRightIntegrand u := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr_Ioo_of_le ha0.le
    intro u hu
    dsimp only [Function.comp_apply]
    rw [show (1 : ℝ) - ((120 / 37) * (1 - u ^ 2)) / (120 / 37) = u ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos hu.1]
    unfold sieveRightIntegrand
    have hu1 : u < 1 := lt_trans hu.2 (lt_trans ha.2 (by norm_num))
    have hden : 1 - u ^ 2 ≠ 0 := by nlinarith [hu.1]
    field_simp [ne_of_gt hu.1, hden]
  have hend : (120 / 37 : ℝ) * (1 - sieveEndpoint ^ 2) = 2 := by rw [ha2]; norm_num
  rw [show (120 / 37 : ℝ) * (1 - (0 : ℝ) ^ 2) = 120 / 37 by norm_num] at hsub
  rw [hend, he] at hsub
  rw [intervalIntegral.integral_symm (a := (2 : ℝ)) (b := 120 / 37)] at hsub
  linarith

/-- Continuity makes the transformed right integrand integrable below 31/50. -/
theorem sieveRightIntegrand_integrable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 31 / 50) :
    IntervalIntegrable sieveRightIntegrand volume a b := by
  have hd : ∀ u ∈ Icc a b, 0 < 1 - u ^ 2 := by
    intro u hu
    have hu0 := ha.trans hu.1
    have hu1 := hu.2.trans hb
    nlinarith
  have hy : ∀ u ∈ Icc a b, 0 < (120 / 37 : ℝ) * (1 - u ^ 2) - 1 := by
    intro u hu
    have hu0 := ha.trans hu.1
    have hu1 := hu.2.trans hb
    nlinarith
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  unfold sieveRightIntegrand
  have hdc : ContinuousOn (fun u : ℝ => 1 - u ^ 2) (Icc a b) := by fun_prop
  have hyc : ContinuousOn (fun u : ℝ => (120 / 37) * (1 - u ^ 2) - 1) (Icc a b) := by fun_prop
  exact (hyc.log (fun u hu => (hy u hu).ne')).div hdc (fun u hu => (hd u hu).ne')

/-- The tangent majorants are integrable on every segment used below. -/
theorem sieveTangent_integrable (L : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 31 / 50) :
    IntervalIntegrable (sieveTangent L) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  have hd : ∀ u ∈ Icc a b, 1 - u ^ 2 ≠ 0 := by
    intro u hu
    have hu0 := ha.trans hu.1
    have hu1 := hu.2.trans hb
    nlinarith
  have hdc : ContinuousOn (fun u : ℝ => 1 - u ^ 2) (Icc a b) := by fun_prop
  unfold sieveTangent
  exact continuousOn_const.add (continuousOn_const.div hdc hd)

/-- A tangent majorant bounds the integral over a segment. -/
theorem sieve_right_segment_bound {L a b : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 31 / 50) :
    (∫ u in a..b, sieveRightIntegrand u) ≤ ∫ u in a..b, sieveTangent L u := by
  apply integral_mono_on hab (sieveRightIntegrand_integrable ha hab hb)
    (sieveTangent_integrable L ha hab hb)
  intro u hu
  exact sieveRightIntegrand_le_tangent hL (ha.trans hu.1) (hu.2.trans hb)

/-- A lower log bound keeps the final tangent nonnegative on the enlarged interval. -/
theorem sieve_last_tangent_nonneg {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 31 / 50) :
    0 ≤ sieveTangent (11 / 10) u := by
  have hl : (945 : ℝ) / 10000 ≤ Real.log (11 / 10 : ℝ) := by
    have h := log_lower_of_power (x := (11 / 10 : ℝ))
      (y := 1 + (955 : ℝ) / 10000 / 16) 16 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hd : 0 < 1 - u ^ 2 := by nlinarith
  unfold sieveTangent
  apply (mul_nonneg_iff_of_pos_right hd).mp
  have he : ((120 / 37 : ℝ) / (11 / 10) +
      (Real.log (11 / 10) - 1 - 1 / (11 / 10)) / (1 - u ^ 2)) * (1 - u ^ 2) =
      ((120 / 37) / (11 / 10)) * (1 - u ^ 2) + (Real.log (11 / 10) - 1 - 1 / (11 / 10)) := by
    field_simp
  rw [he]
  nlinarith

/-- The four segments bound the transformed integral. -/
theorem sieve_right_integral_le_closed :
    (40 / 19 : ℝ) * (∫ u in (0 : ℝ)..sieveEndpoint, sieveRightIntegrand u) ≤ sieveRightClosed := by
  have ha := sieveEndpoint_bounds
  have ha0 : 0 ≤ sieveEndpoint := by linarith
  have hseg1 := sieve_right_segment_bound (L := (11 : ℝ) / 5)
    (a := 0) (b := 1 / 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hseg2 := sieve_right_segment_bound (L := (19 : ℝ) / 10)
    (a := 1 / 5) (b := 2 / 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hseg3 := sieve_right_segment_bound (L := (7 : ℝ) / 5)
    (a := 2 / 5) (b := 11 / 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hseg4 := sieve_right_segment_bound (L := (11 : ℝ) / 10)
    (a := 11 / 20) (b := sieveEndpoint) (by norm_num) (by norm_num) ha.1.le ha.2.le
  have hext : (∫ u in (11 : ℝ) / 20..sieveEndpoint, sieveTangent (11 / 10) u) ≤
      ∫ u in (11 : ℝ) / 20..(31 / 50), sieveTangent (11 / 10) u := by
    apply integral_mono_interval (le_refl _) ha.1.le ha.2.le
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact sieve_last_tangent_nonneg (by linarith [hu.1]) hu.2
    · exact sieveTangent_integrable _ (by norm_num) (by norm_num) (by norm_num)
  have hi1 := sieveRightIntegrand_integrable (a := 0) (b := 1 / 5) (by norm_num) (by norm_num) (by norm_num)
  have hi2 := sieveRightIntegrand_integrable (a := 1 / 5) (b := 2 / 5) (by norm_num) (by norm_num) (by norm_num)
  have hi3 := sieveRightIntegrand_integrable (a := 2 / 5) (b := 11 / 20) (by norm_num) (by norm_num) (by norm_num)
  have hi4 := sieveRightIntegrand_integrable (a := 11 / 20) (b := sieveEndpoint) (by norm_num) ha.1.le ha.2.le
  have hsplit : (∫ u in (0 : ℝ)..sieveEndpoint, sieveRightIntegrand u) =
      (∫ u in (0 : ℝ)..(1 / 5), sieveRightIntegrand u) +
      (∫ u in (1 : ℝ) / 5..(2 / 5), sieveRightIntegrand u) +
      (∫ u in (2 : ℝ) / 5..(11 / 20), sieveRightIntegrand u) +
      (∫ u in (11 : ℝ) / 20..sieveEndpoint, sieveRightIntegrand u) := by
    rw [← integral_add_adjacent_intervals (hi1.trans hi2 |>.trans hi3) hi4,
      ← integral_add_adjacent_intervals (hi1.trans hi2) hi3,
      ← integral_add_adjacent_intervals hi1 hi2]
  rw [integral_sieveTangent (11 / 5) (a := 0) (b := 1 / 5)
    (by norm_num) (by norm_num) (by norm_num)] at hseg1
  rw [integral_sieveTangent (19 / 10) (a := 1 / 5) (b := 2 / 5)
    (by norm_num) (by norm_num) (by norm_num)] at hseg2
  rw [integral_sieveTangent (7 / 5) (a := 2 / 5) (b := 11 / 20)
    (by norm_num) (by norm_num) (by norm_num)] at hseg3
  rw [integral_sieveTangent (11 / 10) (a := 11 / 20) (b := 31 / 50)
    (by norm_num) (by norm_num) (by norm_num)] at hext
  norm_num only [] at hseg1 hseg2 hseg3 hext
  unfold sieveRightClosed
  rw [hsplit]
  norm_num at hseg1 hseg2 hseg3 hext ⊢
  linarith

/-- The analytic comparison in SieveMargin is now discharged. -/
theorem sieve_integral_bounds_proved : SieveIntegralBounds := by
  constructor
  · exact (sieve_left_integral_eq (by norm_num : (0 : ℝ) < 57 / 140) (by norm_num)).ge
  · rw [show (1 : ℝ) / (2 * (19 / 40)) = 20 / 19 by norm_num, sieve_right_substitution]
    exact sieve_right_integral_le_closed

/-- The page 47 sieve inequality at theta = 1/80, without an integral hypothesis. -/
theorem sieveH_theta_proved : SieveH (19 / 40) (57 / 140) (120 / 37) :=
  sieveH_theta_of_integral_bounds sieve_integral_bounds_proved

/-- The page 47 parameters lie in the domain of Definition 6.3. -/
theorem sieve_theta_parameters_admissible :
    (1 : ℝ) / 3 < 57 / 140 ∧ (57 : ℝ) / 140 < 19 / 40 ∧
      (19 : ℝ) / 40 < 1 / 2 ∧ (3 : ℝ) < 120 / 37 ∧ (120 : ℝ) / 37 < 4 := by
  norm_num

/-- The actual integral difference exceeds the printed page 47 margin. -/
theorem sieve_actual_margin : (1 : ℝ) / 1000 <
    1 / (2 * Real.sqrt (57 / 140)) *
      (∫ t in (1 : ℝ)..((57 / 140) * (120 / 37)), 1 / Real.sqrt (t * (t - 1))) -
    1 / (2 * (19 / 40 : ℝ)) * (∫ t in (2 : ℝ)..(120 / 37),
      Real.log (t - 1) / (t * Real.sqrt (1 - t / (120 / 37)))) := by
  obtain ⟨hL, hR⟩ := sieve_integral_bounds_proved
  linarith [sieve_closed_margin]

#print axioms sieve_theta_parameters_admissible
#print axioms sieve_actual_margin

#print axioms sieveEndpoint_bounds
#print axioms sieve_right_substitution
#print axioms sieveRightIntegrand_integrable
#print axioms sieveTangent_integrable
#print axioms sieve_right_segment_bound
#print axioms sieve_last_tangent_nonneg
#print axioms sieve_right_integral_le_closed
#print axioms sieve_integral_bounds_proved
#print axioms sieveH_theta_proved

end LeanLab.Teravainen2016
