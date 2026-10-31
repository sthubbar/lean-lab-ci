/-
P0076 Definition 6.3, page 21, and the numerical margin at theta = 1/80 on page 47.
The integral comparison is kept explicit. Only certified closed expression bounds are proved here.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Restriction

open MeasureTheory intervalIntegral

namespace LeanLab.Teravainen2016

/-- The inequality H of display 6.1. -/
def SieveH (ρ₁ ρ₂ σ : ℝ) : Prop :=
  1 / (2 * Real.sqrt ρ₂) * (∫ t in (1 : ℝ)..(ρ₂ * σ), 1 / Real.sqrt (t * (t - 1))) >
    1 / (2 * ρ₁) * (∫ t in (2 : ℝ)..σ,
      Real.log (t - 1) / (t * Real.sqrt (1 - t / σ))) + 1 / (10 : ℝ) ^ 10

/-- A rational power certificate gives an upper logarithm bound. -/
theorem log_upper_of_power {x y : ℝ} (n : ℕ) (hx : 0 < x) (hy : 0 < y) (hp : x ≤ y ^ n) :
    Real.log x ≤ (n : ℝ) * (y - 1) := by
  have h1 := Real.log_le_log hx hp
  rw [Real.log_pow] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hy) (by positivity))

/-- A rational power certificate gives a lower logarithm bound. -/
theorem log_lower_of_power {x y : ℝ} (n : ℕ) (hx : 0 < x) (hy : 0 < y) (hp : y ^ n ≤ x) :
    (n : ℝ) * (1 - y⁻¹) ≤ Real.log x := by
  have h1 := Real.log_le_log (pow_pos hy n) hp
  rw [Real.log_pow] at h1
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
  rw [Real.log_inv] at h2
  exact (mul_le_mul_of_nonneg_left (by linarith : 1 - y⁻¹ ≤ Real.log y) (by positivity)).trans h1

set_option maxRecDepth 10000
set_option exponentiation.threshold 2048
set_option maxHeartbeats 2000000

theorem log_eleven_fifths_upper : Real.log (11 / 5 : ℝ) ≤ 789 / 1000 := by
  have h := log_upper_of_power (x := (11 / 5 : ℝ)) (y := 1 + (789 / 1000 : ℝ) / 1024) 1024
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem log_nineteen_tenths_upper : Real.log (19 / 10 : ℝ) ≤ 643 / 1000 := by
  have h := log_upper_of_power (x := (19 / 10 : ℝ)) (y := 1 + (643 / 1000 : ℝ) / 1024) 1024
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem log_seven_fifths_upper : Real.log (7 / 5 : ℝ) ≤ 337 / 1000 := by
  have h := log_upper_of_power (x := (7 / 5 : ℝ)) (y := 1 + (337 / 1000 : ℝ) / 1024) 1024
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem log_eleven_tenths_upper : Real.log (11 / 10 : ℝ) ≤ 96 / 1000 := by
  have h := log_upper_of_power (x := (11 / 10 : ℝ)) (y := 1 + (96 / 1000 : ℝ) / 1024) 1024
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem log_three_halves_lower : (405 / 1000 : ℝ) ≤ Real.log (3 / 2 : ℝ) := by
  have h := log_lower_of_power (x := (3 / 2 : ℝ)) (y := 1 + (4052 / 10000 : ℝ) / 1024) 1024
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

theorem log_fourteen_ninths_lower : (441 / 1000 : ℝ) ≤ Real.log (14 / 9 : ℝ) := by
  have h := log_lower_of_power (x := (14 / 9 : ℝ)) (y := 1 + (4412 / 10000 : ℝ) / 1024) 1024
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

theorem log_thirtyone_twentyfirsts_lower : (389 / 1000 : ℝ) ≤ Real.log (31 / 21 : ℝ) := by
  have h := log_lower_of_power (x := (31 / 21 : ℝ)) (y := 1 + (3892 / 10000 : ℝ) / 1024) 1024
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

theorem log_ratio_last_lower : (213 / 1000 : ℝ) ≤ Real.log (729 / 589 : ℝ) := by
  have h := log_lower_of_power (x := (729 / 589 : ℝ)) (y := 1 + (2132 / 10000 : ℝ) / 1024) 1024
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

theorem log_left_argument_lower : (5393 / 10000 : ℝ) ≤ Real.log (171519 / 100000 : ℝ) := by
  have h := log_lower_of_power (x := (171519 / 100000 : ℝ)) (y := 1 + (5395 / 10000 : ℝ) / 2048) 2048
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

/-- The elementary closed expression for the left integral after substitution. -/
noncomputable def sieveLeftClosed (ρ₂ σ : ℝ) : ℝ :=
  Real.log (Real.sqrt (ρ₂ * σ) + Real.sqrt (ρ₂ * σ - 1)) / Real.sqrt ρ₂

/-- One integrated tangent segment in the transformed right integral. -/
noncomputable def sieveTangentTerm (L width ratio : ℝ) : ℝ :=
  (120 / 37) / L * width + (Real.log L - 1 - 1 / L) * (Real.log ratio / 2)

/-- Four tangent segments, with endpoints 0, 1/5, 2/5, 11/20 and 31/50. -/
noncomputable def sieveRightClosed : ℝ := (40 / 19) *
  (sieveTangentTerm (11 / 5) (1 / 5) (3 / 2) +
   sieveTangentTerm (19 / 10) (1 / 5) (14 / 9) +
   sieveTangentTerm (7 / 5) (3 / 20) (31 / 21) +
   sieveTangentTerm (11 / 10) (7 / 100) (729 / 589))

/-- Monotonicity with the signs needed for the tangent coefficients. -/
theorem sieveTangentTerm_le {L width ratio U V : ℝ}
    (hlog : Real.log L ≤ U) (hU : U ≤ 1 + 1 / L)
    (hV : 0 ≤ V) (hratio : V ≤ Real.log ratio / 2) :
    sieveTangentTerm L width ratio ≤ (120 / 37) / L * width + (U - 1 - 1 / L) * V := by
  have ha : Real.log L - 1 - 1 / L ≤ 0 := by linarith
  have h1 := mul_le_mul_of_nonpos_left hratio ha
  have h2 := mul_le_mul_of_nonneg_right
    (show Real.log L - 1 - 1 / L ≤ U - 1 - 1 / L by linarith) hV
  unfold sieveTangentTerm
  linarith

/-- A certified lower bound for the closed left expression at theta = 1/80. -/
theorem sieveLeftClosed_lower : (845 : ℝ) / 1000 ≤ sieveLeftClosed (57 / 140) (120 / 37) := by
  have h1 : (11491 : ℝ) / 10000 ≤ Real.sqrt ((57 / 140) * (120 / 37)) :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h2 : (56609 : ℝ) / 100000 ≤ Real.sqrt ((57 / 140) * (120 / 37) - 1) :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h3 : Real.sqrt (57 / 140 : ℝ) ≤ 63808 / 100000 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hlog : (5393 : ℝ) / 10000 ≤
      Real.log (Real.sqrt ((57 / 140) * (120 / 37)) + Real.sqrt ((57 / 140) * (120 / 37) - 1)) :=
    log_left_argument_lower.trans (Real.log_le_log (by norm_num) (by linarith))
  unfold sieveLeftClosed
  rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 57 / 140))]
  nlinarith

/-- A certified upper bound for the four tangent expression. -/
theorem sieveRightClosed_upper : sieveRightClosed ≤ (842 : ℝ) / 1000 := by
  have h1 := sieveTangentTerm_le (width := (1 : ℝ) / 5) log_eleven_fifths_upper
    (by norm_num : (789 : ℝ) / 1000 ≤ 1 + 1 / (11 / 5)) (by norm_num : (0 : ℝ) ≤ 2025 / 10000)
    (show (2025 : ℝ) / 10000 ≤ Real.log (3 / 2 : ℝ) / 2 by linarith [log_three_halves_lower])
  have h2 := sieveTangentTerm_le (width := (1 : ℝ) / 5) log_nineteen_tenths_upper
    (by norm_num : (643 : ℝ) / 1000 ≤ 1 + 1 / (19 / 10)) (by norm_num : (0 : ℝ) ≤ 2205 / 10000)
    (show (2205 : ℝ) / 10000 ≤ Real.log (14 / 9 : ℝ) / 2 by linarith [log_fourteen_ninths_lower])
  have h3 := sieveTangentTerm_le (width := (3 : ℝ) / 20) log_seven_fifths_upper
    (by norm_num : (337 : ℝ) / 1000 ≤ 1 + 1 / (7 / 5)) (by norm_num : (0 : ℝ) ≤ 1945 / 10000)
    (show (1945 : ℝ) / 10000 ≤ Real.log (31 / 21 : ℝ) / 2 by linarith [log_thirtyone_twentyfirsts_lower])
  have h4 := sieveTangentTerm_le (width := (7 : ℝ) / 100) log_eleven_tenths_upper
    (by norm_num : (96 : ℝ) / 1000 ≤ 1 + 1 / (11 / 10)) (by norm_num : (0 : ℝ) ≤ 1065 / 10000)
    (show (1065 : ℝ) / 10000 ≤ Real.log (729 / 589 : ℝ) / 2 by linarith [log_ratio_last_lower])
  unfold sieveRightClosed
  norm_num at h1 h2 h3 h4 ⊢
  linarith

/-- The closed expressions have more than the printed numerical margin. -/
theorem sieve_closed_margin : (1 : ℝ) / 1000 <
    sieveLeftClosed (57 / 140) (120 / 37) - sieveRightClosed := by
  linarith [sieveLeftClosed_lower, sieveRightClosed_upper]

/-- The analytic comparison still required to turn the closed certificates into display 6.1. -/
def SieveIntegralBounds : Prop :=
  sieveLeftClosed (57 / 140) (120 / 37) ≤
    1 / (2 * Real.sqrt (57 / 140)) *
      (∫ t in (1 : ℝ)..((57 / 140) * (120 / 37)), 1 / Real.sqrt (t * (t - 1))) ∧
  1 / (2 * (19 / 40 : ℝ)) * (∫ t in (2 : ℝ)..(120 / 37),
    Real.log (t - 1) / (t * Real.sqrt (1 - t / (120 / 37)))) ≤ sieveRightClosed

/-- The page 47 parameter inequality, CONDITIONAL ON the explicit integral comparison. -/
theorem sieveH_theta_of_integral_bounds (h : SieveIntegralBounds) :
    SieveH (19 / 40) (57 / 140) (120 / 37) := by
  obtain ⟨hL, hR⟩ := h
  have hm := sieve_closed_margin
  unfold SieveH
  norm_num at hL hR hm ⊢
  linarith

#print axioms sieveTangentTerm_le
#print axioms sieveLeftClosed_lower
#print axioms sieveRightClosed_upper
#print axioms sieve_closed_margin
#print axioms sieveH_theta_of_integral_bounds

#print axioms log_eleven_fifths_upper

#print axioms log_nineteen_tenths_upper

#print axioms log_seven_fifths_upper

#print axioms log_eleven_tenths_upper

#print axioms log_three_halves_lower

#print axioms log_fourteen_ninths_lower

#print axioms log_thirtyone_twentyfirsts_lower

#print axioms log_ratio_last_lower

#print axioms log_left_argument_lower

#print axioms log_upper_of_power
#print axioms log_lower_of_power

end LeanLab.Teravainen2016
