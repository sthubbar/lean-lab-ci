import LeanLab.ChirreHagen2025.Statements

/-!
Scalar audit of Johnston, Ramare and Trudgian 2023 page 3 Lemma 9,
read for P0075 page 3 and Decomp358d.mangoldt_large_range.
https://arxiv.org/abs/2303.13785
This checks the literal displayed error function, not Lemma 10 itself.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Audit429

/-- JRT page 3, the literal displayed error function in Lemma 9.
The printed branch threshold is 2R log squared T0, without an exponential. -/
noncomputable def literalError (x : ℝ) : ℝ :=
  if x < 2 * 5.69693 * Real.log (2.44 * 10 ^ 12) ^ 2 then 1.75 / 10 ^ 12
  else (1 + 2 * Real.sqrt (Real.log x / 5.69693)) / (2 * Real.pi) *
    Real.exp (-2 * Real.sqrt (Real.log x / 5.69693))

/-- JRT page 4, elementary logarithm bounds at the stated analytic cutoff. -/
theorem cutoff_log_bounds : 11 ≤ Real.log (100000 : ℝ) ∧ Real.log (100000 : ℝ) ≤ 12 := by
  constructor
  · rw [Real.le_log_iff_exp_le (by norm_num)]
    calc
      Real.exp 11 = Real.exp 1 ^ (11 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.72 : ℝ) ^ 11 := by gcongr; linarith [Real.exp_one_lt_d9]
      _ ≤ 100000 := by norm_num
  · rw [Real.log_le_iff_le_exp (by norm_num)]
    calc
      (100000 : ℝ) ≤ (2.7 : ℝ) ^ 12 := by norm_num
      _ ≤ Real.exp 1 ^ 12 := by gcongr; linarith [Real.exp_one_gt_d9]
      _ = Real.exp 12 := by rw [← Real.exp_nat_mul]; norm_num

/-- JRT page 3, its literal transition point lies below the cutoff in Lemma 10. -/
theorem literal_transition_lt_cutoff :
    2 * (5.69693 : ℝ) * Real.log (2.44 * 10 ^ 12) ^ 2 < 100000 := by
  have hl0 : 0 ≤ Real.log (2.44 * 10 ^ 12 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : Real.log (2.44 * 10 ^ 12 : ℝ) ≤ 30 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc
      (2.44 * 10 ^ 12 : ℝ) ≤ (2.7 : ℝ) ^ 30 := by norm_num
      _ ≤ Real.exp 1 ^ 30 := by gcongr; linarith [Real.exp_one_gt_d9]
      _ = Real.exp 30 := by rw [← Real.exp_nat_mul]; norm_num
  have hs := pow_le_pow_left₀ hl0 hl 2
  nlinarith

/-- JRT page 3 literal Lemma 9 error and page 4 claimed 0.67 budget.
The printed error alone exceeds that whole budget at the analytic cutoff.
This is a scalar QUESTION about the route, not a refutation of Lemma 10. -/
theorem literal_error_exceeds_budget :
    0.67 / Real.log (100000 : ℝ) ^ 2 < literalError 100000 := by
  have hl := cutoff_log_bounds
  have hq0 : 0 ≤ Real.log (100000 : ℝ) / 5.69693 := by positivity
  have hs : Real.sqrt (Real.log (100000 : ℝ) / 5.69693) ≤ 3 / 2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5.69693)).mpr
      linarith
  have he3 : Real.exp (3 : ℝ) ≤ 21 := by
    calc
      Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.72 : ℝ) ^ 3 := by gcongr; linarith [Real.exp_one_lt_d9]
      _ ≤ 21 := by norm_num
  have he : (1 / 21 : ℝ) ≤
      Real.exp (-2 * Real.sqrt (Real.log (100000 : ℝ) / 5.69693)) := by
    calc
      (1 / 21 : ℝ) ≤ (Real.exp 3)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos 3) he3
      _ = Real.exp (-3) := (Real.exp_neg 3).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hr : (1 / 8 : ℝ) ≤
      (1 + 2 * Real.sqrt (Real.log (100000 : ℝ) / 5.69693)) / (2 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith [Real.sqrt_nonneg (Real.log (100000 : ℝ) / 5.69693), Real.pi_lt_four]
  have hprod := mul_le_mul hr he (by norm_num : (0 : ℝ) ≤ 1 / 21)
    (by positivity : 0 ≤ (1 + 2 * Real.sqrt (Real.log (100000 : ℝ) / 5.69693)) / (2 * Real.pi))
  have htarget : 0.67 / Real.log (100000 : ℝ) ^ 2 ≤ (0.67 / 121 : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 121)
    nlinarith
  unfold literalError
  rw [if_neg (not_lt.mpr literal_transition_lt_cutoff.le)]
  exact htarget.trans_lt (lt_of_lt_of_le (by norm_num : (0.67 / 121 : ℝ) < (1 / 8) * (1 / 21)) hprod)

end LeanLab.ChirreHagen2025.Audit429
