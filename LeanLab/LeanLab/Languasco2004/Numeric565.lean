/-
Jia 1996 pages 283 to 285, displays 60 and 64 and the remaining seven regions.
Source https://doi.org/10.4064/aa-77-3-207-287.
These are certified numerical integrals. Prime distribution is not asserted.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.LogApprox565
import LeanLab.Languasco2004.Integral565

namespace LeanLab.Languasco2004.Numeric565
open Finset Real intervalIntegral LogApprox565
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Pages 283 to 285: the reduced source integral for mainOne. -/
def mainOne : ℝ := (0.5612 * (135 / 16)) * (∫ t in (16 / 135 : ℝ)..(89 / 462 : ℝ), log (0 + (135 / 16) * t) / t) - 0.000001

/-- Pages 283 to 285: certify the printed 0.558649 bound for mainOne. -/
theorem mainOne_bound : (0.558649 : ℝ) ≤ mainOne := by
  have h0 := integral_log_approx (16 / 135 : ℝ) (89 / 462 : ℝ) (0) (135 / 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨h0L, h0U⟩ := abs_le.mp h0
  have hc : (0.558649 : ℝ) + 0.000001 + (0.5612 * (135 / 16)) * (0.00000002 * ((89 / 462 : ℝ) - (16 / 135 : ℝ)) * 1) ≤ (0.5612 * (135 / 16)) * (∫ t in (16 / 135 : ℝ)..(89 / 462 : ℝ), logPoly (0 + (135 / 16) * t) * recipPoly (89 / 462 : ℝ) t) := by
    unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  unfold mainOne
  nlinarith

/-- Pages 283 to 285: the reduced source integral for tripleOne. -/
def tripleOne : ℝ := (0.5617 * (135 / 32)) * (∫ t in (16 / 135 : ℝ)..(71 / 405 : ℝ), (log (0 + (135 / 16) * t))^2 / t)

/-- Pages 283 to 285: certify the printed 0.047392 bound for tripleOne. -/
theorem tripleOne_bound : tripleOne ≤ (0.047392 : ℝ) := by
  have h0 := integral_logsq_approx (16 / 135 : ℝ) (71 / 405 : ℝ) (0) (135 / 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨h0L, h0U⟩ := abs_le.mp h0
  have hc : (0.5617 * (135 / 32)) * (∫ t in (16 / 135 : ℝ)..(71 / 405 : ℝ), (logPoly (0 + (135 / 16) * t))^2 * recipPoly (71 / 405 : ℝ) t) + (0.5617 * (135 / 32)) * (0.00000004 * ((71 / 405 : ℝ) - (16 / 135 : ℝ)) * 1) ≤ (0.047392 : ℝ) := by
    unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  unfold tripleOne
  nlinarith

/-- Pages 283 to 285: the reduced source integral for tripleTwo. -/
def tripleTwo : ℝ := (0.5617 * (135 / 32)) * (∫ t in (71 / 405 : ℝ)..(89 / 462 : ℝ), (log (71 / 32 + (-135 / 32) * t))^2 / t)

/-- Pages 283 to 285: certify the printed 0.030099 bound for tripleTwo. -/
theorem tripleTwo_bound : tripleTwo ≤ (0.030099 : ℝ) := by
  have h0 := integral_logsq_approx (71 / 405 : ℝ) (89 / 462 : ℝ) (71 / 32) (-135 / 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨h0L, h0U⟩ := abs_le.mp h0
  have hc : (0.5617 * (135 / 32)) * (∫ t in (71 / 405 : ℝ)..(89 / 462 : ℝ), (logPoly (71 / 32 + (-135 / 32) * t))^2 * recipPoly (89 / 462 : ℝ) t) + (0.5617 * (135 / 32)) * (0.00000004 * ((89 / 462 : ℝ) - (71 / 405 : ℝ)) * 1) ≤ (0.030099 : ℝ) := by
    unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  unfold tripleTwo
  nlinarith

/-- Pages 283 to 285: the reduced source integral for tripleThree. -/
def tripleThree : ℝ := (0.5644 * (135 / 32)) * ((∫ t in (71 / 405 : ℝ)..(89 / 462 : ℝ), (log (0 + (135 / 16) * t))^2 / t) - (∫ t in (71 / 405 : ℝ)..(89 / 462 : ℝ), (log (71 / 32 + (-135 / 32) * t))^2 / t))

/-- Pages 283 to 285: certify the printed 0.013113 bound for tripleThree. -/
theorem tripleThree_bound : tripleThree ≤ (0.013113 : ℝ) := by
  have h0 := integral_logsq_approx (71 / 405 : ℝ) (89 / 462 : ℝ) (0) (135 / 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨h0L, h0U⟩ := abs_le.mp h0
  have h1 := integral_logsq_approx (71 / 405 : ℝ) (89 / 462 : ℝ) (71 / 32) (-135 / 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨h1L, h1U⟩ := abs_le.mp h1
  have hc : (0.5644 * (135 / 32)) * ((∫ t in (71 / 405 : ℝ)..(89 / 462 : ℝ), (logPoly (0 + (135 / 16) * t))^2 * recipPoly (89 / 462 : ℝ) t) - (∫ t in (71 / 405 : ℝ)..(89 / 462 : ℝ), (logPoly (71 / 32 + (-135 / 32) * t))^2 * recipPoly (89 / 462 : ℝ) t)) + (0.5644 * (135 / 32)) * (0.00000004 * ((89 / 462 : ℝ) - (71 / 405 : ℝ)) * 2) ≤ (0.013113 : ℝ) := by
    unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  unfold tripleThree
  nlinarith

/-- Pages 283 to 285: the reduced source integral for mainRest. -/
def mainRest : ℝ := (0.5612 * (135 / 16)) * (∫ t in (89 / 462 : ℝ)..(17 / 54 : ℝ), log (1335 / 512 + (-1305 / 256) * t) / t) - 0.000001

/-- Pages 283 to 285: certify the printed 0.658048 bound for mainRest. -/
theorem mainRest_bound : (0.658048 : ℝ) ≤ mainRest := by
  have h0 := integral_log_approx (89 / 462 : ℝ) (17 / 54 : ℝ) (1335 / 512) (-1305 / 256)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨h0L, h0U⟩ := abs_le.mp h0
  have hc : (0.658048 : ℝ) + 0.000001 + (0.5612 * (135 / 16)) * (0.00000002 * ((17 / 54 : ℝ) - (89 / 462 : ℝ)) * 1) ≤ (0.5612 * (135 / 16)) * (∫ t in (89 / 462 : ℝ)..(17 / 54 : ℝ), logPoly (1335 / 512 + (-1305 / 256) * t) * recipPoly (17 / 54 : ℝ) t) := by
    unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  unfold mainRest
  nlinarith

/-- Pages 283 to 285: the reduced source integral for restOne. -/
def restOne : ℝ := (0.5617 * (135 / 32)) * (∫ t in (89 / 462 : ℝ)..(13 / 45 : ℝ), (log (71 / 32 + (-135 / 32) * t))^2 / t)

/-- Pages 283 to 285: certify the printed 0.044320 bound for restOne. -/
theorem restOne_bound : restOne ≤ (0.044320 : ℝ) := by
  have h0 := integral_logsq_approx (89 / 462 : ℝ) (13 / 45 : ℝ) (71 / 32) (-135 / 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨h0L, h0U⟩ := abs_le.mp h0
  have hc : (0.5617 * (135 / 32)) * (∫ t in (89 / 462 : ℝ)..(13 / 45 : ℝ), (logPoly (71 / 32 + (-135 / 32) * t))^2 * recipPoly (13 / 45 : ℝ) t) + (0.5617 * (135 / 32)) * (0.00000004 * ((13 / 45 : ℝ) - (89 / 462 : ℝ)) * 1) ≤ (0.044320 : ℝ) := by
    unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  unfold restOne
  nlinarith

/-- Pages 283 to 285: the reduced source integral for restTwo. -/
def restTwo : ℝ := (0.5644 * (135 / 32)) * ((∫ t in (89 / 462 : ℝ)..(13 / 45 : ℝ), (log (1335 / 512 + (-1305 / 256) * t))^2 / t) - (∫ t in (89 / 462 : ℝ)..(13 / 45 : ℝ), (log (71 / 32 + (-135 / 32) * t))^2 / t))

/-- Pages 283 to 285: certify the printed 0.069979 bound for restTwo. -/
theorem restTwo_bound : restTwo ≤ (0.069979 : ℝ) := by
  have h0 := integral_logsq_approx (89 / 462 : ℝ) (13 / 45 : ℝ) (1335 / 512) (-1305 / 256)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨h0L, h0U⟩ := abs_le.mp h0
  have h1 := integral_logsq_approx (89 / 462 : ℝ) (13 / 45 : ℝ) (71 / 32) (-135 / 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨h1L, h1U⟩ := abs_le.mp h1
  have hc : (0.5644 * (135 / 32)) * ((∫ t in (89 / 462 : ℝ)..(13 / 45 : ℝ), (logPoly (1335 / 512 + (-1305 / 256) * t))^2 * recipPoly (13 / 45 : ℝ) t) - (∫ t in (89 / 462 : ℝ)..(13 / 45 : ℝ), (logPoly (71 / 32 + (-135 / 32) * t))^2 * recipPoly (13 / 45 : ℝ) t)) + (0.5644 * (135 / 32)) * (0.00000004 * ((13 / 45 : ℝ) - (89 / 462 : ℝ)) * 2) ≤ (0.069979 : ℝ) := by
    unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  unfold restTwo
  nlinarith

/-- Pages 283 to 285: the reduced source integral for restThree. -/
def restThree : ℝ := (0.5644 * (135 / 32)) * (∫ t in (13 / 45 : ℝ)..(17 / 54 : ℝ), (log (1335 / 512 + (-1305 / 256) * t))^2 / t)

/-- Pages 283 to 285: certify the printed 0.001171 bound for restThree. -/
theorem restThree_bound : restThree ≤ (0.001171 : ℝ) := by
  have h0 := integral_logsq_approx (13 / 45 : ℝ) (17 / 54 : ℝ) (1335 / 512) (-1305 / 256)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨h0L, h0U⟩ := abs_le.mp h0
  have hc : (0.5644 * (135 / 32)) * (∫ t in (13 / 45 : ℝ)..(17 / 54 : ℝ), (logPoly (1335 / 512 + (-1305 / 256) * t))^2 * recipPoly (17 / 54 : ℝ) t) + (0.5644 * (135 / 32)) * (0.00000004 * ((17 / 54 : ℝ) - (13 / 45 : ℝ)) * 1) ≤ (0.001171 : ℝ) := by
    unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  unfold restThree
  nlinarith

/-- Display 64: the certified main term minus all three subtraction terms gives 0.468045. -/
theorem region1_numeric : (0.468045 : ℝ) ≤ mainOne - tripleOne - tripleTwo - tripleThree := by
  nlinarith [mainOne_bound, tripleOne_bound, tripleTwo_bound, tripleThree_bound]

/-- Page 285: the seven remaining regions give the certified coefficient 0.542578. -/
theorem remainder_numeric : (0.542578 : ℝ) ≤ mainRest - restOne - restTwo - restThree := by
  nlinarith [mainRest_bound, restOne_bound, restTwo_bound, restThree_bound]

#print axioms mainOne_bound
#print axioms tripleOne_bound
#print axioms tripleTwo_bound
#print axioms tripleThree_bound
#print axioms mainRest_bound
#print axioms restOne_bound
#print axioms restTwo_bound
#print axioms restThree_bound
#print axioms region1_numeric
#print axioms remainder_numeric
end
end LeanLab.Languasco2004.Numeric565
