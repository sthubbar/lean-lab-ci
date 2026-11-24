/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit xiPrime_1e8.
Schoenfeld 1976, Math. Comp. 30, p. 340 line 1: "Taking ξ = 10⁸, we obtain ξ' ≅ 88.26",
where display (6.19b) defines ξ' = {li ξ - π ξ} - {ξ - θ ξ} / log ξ.
This file splits that numerical evaluation into the three values it uses, each a LEAF,
and proves the rest: the bounds on log 10⁸ and the arithmetic giving |ξ'| < 89, the
rounded margin used by SchoenfeldCor1S63.xiPrime_1e8.
Values computed in this unit with Python and mpmath: π 10⁸ = 5761455,
θ 10⁸ = 99987730.0180, li 10⁸ = 5762209.3754, so ξ' = 88.277, which is within the
paper's 88.26 up to its rounding; the margin to 89 is about 0.72.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.PaperInputs148
import LeanLab.BS2022GRH.LiPV

namespace LeanLab.BS2022GRH.SchoenfeldXiS70
open Real LeanLab.BS2022GRH.PaperInputs148

/-- LEAF: Schoenfeld 1976 p. 340 line 1, the value of π ξ at ξ = 10⁸ used in ξ'.
`π 10⁸ = 5761455`, the classical value. MEDIUM, a prime count to 10⁸. -/
theorem primeCount_1e8 : primeCount (10 ^ 8) = 5761455 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, the value of θ ξ at ξ = 10⁸ used in ξ'.
`99987730.01 ≤ θ 10⁸ ≤ 99987730.03`. MEDIUM, a sum of log p over primes to 10⁸. -/
theorem theta_1e8 : 99987730.01 ≤ Chebyshev.theta (10 ^ 8) ∧
    Chebyshev.theta (10 ^ 8) ≤ 99987730.03 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, the value of li ξ at ξ = 10⁸ used in ξ'.
`5762209.37 ≤ li 10⁸ ≤ 5762209.38`, li the principal value integral of [10]. MEDIUM. -/
theorem liPV_1e8 : 5762209.37 ≤ liPV (10 ^ 8) ∧ liPV (10 ^ 8) ≤ 5762209.38 := by
  sorry

/-- PROVED: `18 ≤ log 10⁸`. -/
theorem log_1e8_ge : (18 : ℝ) ≤ log (10 ^ 8) := by
  rw [le_log_iff_exp_le (by norm_num), show (18 : ℝ) = ((18 : ℕ) : ℝ) by norm_num, ← exp_one_pow]
  have h := exp_one_lt_d9
  have h0 : 0 < exp 1 := exp_pos 1
  calc exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 := pow_le_pow_left₀ h0.le h.le 18
    _ ≤ 10 ^ 8 := by norm_num

/-- PROVED: `log 10⁸ ≤ 18.43`. -/
theorem log_1e8_le : log (10 ^ 8) ≤ (18.43 : ℝ) := by
  rw [log_le_iff_le_exp (by norm_num)]
  have he : (18.43 : ℝ) = 18 + 0.215 + 0.215 := by norm_num
  rw [he, exp_add, exp_add, show (18 : ℝ) = ((18 : ℕ) : ℝ) by norm_num, ← exp_one_pow]
  have h1 := exp_one_gt_d9
  have h2 : 1 + 0.215 + (0.215 : ℝ) ^ 2 / 2 ≤ exp 0.215 :=
    quadratic_le_exp_of_nonneg (by norm_num)
  have h3 : (2.7182818283 : ℝ) ^ 18 ≤ exp 1 ^ 18 := pow_le_pow_left₀ (by norm_num) h1.le 18
  have h4 : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ 18 := by positivity
  have h5 : (0 : ℝ) ≤ 1 + 0.215 + (0.215 : ℝ) ^ 2 / 2 := by norm_num
  calc (10 : ℝ) ^ 8 ≤ (2.7182818283 : ℝ) ^ 18 * (1 + 0.215 + (0.215 : ℝ) ^ 2 / 2)
        * (1 + 0.215 + (0.215 : ℝ) ^ 2 / 2) := by norm_num
    _ ≤ exp 1 ^ 18 * exp 0.215 * exp 0.215 := by gcongr

/-- PROVED from the three LEAFs: `|ξ'| < 89` at `ξ = 10⁸`, with
`ξ' = {li ξ - π ξ} - {ξ - θ ξ} / log ξ`, Schoenfeld 1976 display (6.19b). -/
theorem xiPrime_1e8_of_values :
    |(liPV (10 ^ 8) - primeCount (10 ^ 8)) - ((10 ^ 8 : ℝ) - Chebyshev.theta (10 ^ 8)) / log (10 ^ 8)|
      < 89 := by
  have hP := primeCount_1e8
  obtain ⟨hT1, hT2⟩ := theta_1e8
  obtain ⟨hL1, hL2⟩ := liPV_1e8
  have hl1 := log_1e8_ge
  have hl2 := log_1e8_le
  have hl0 : 0 < log ((10 : ℝ) ^ 8) := by linarith
  have hq1 : ((10 ^ 8 : ℝ) - Chebyshev.theta (10 ^ 8)) / log (10 ^ 8) ≤ 682 := by
    rw [div_le_iff₀ hl0]; norm_num at hT1 hl1 ⊢; linarith
  have hq2 : 665.7 ≤ ((10 ^ 8 : ℝ) - Chebyshev.theta (10 ^ 8)) / log (10 ^ 8) := by
    rw [le_div_iff₀ hl0]; norm_num at hT2 hl2 ⊢; linarith
  rw [hP, abs_lt]
  constructor <;> linarith

end LeanLab.BS2022GRH.SchoenfeldXiS70

#print axioms LeanLab.BS2022GRH.SchoenfeldXiS70.log_1e8_ge
#print axioms LeanLab.BS2022GRH.SchoenfeldXiS70.log_1e8_le
#print axioms LeanLab.BS2022GRH.SchoenfeldXiS70.xiPrime_1e8_of_values
