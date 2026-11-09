/- AI wrote the Lean code for CODEX task333. Goldbach is open.
Sign of the journal lower coefficient on the selected table domain.
Journal Table 1 p. 1218 and Theorem 5 pp. 1228 and 1229. -/
import LeanLab.BS2022GRH.DecompC169a

namespace LeanLab.BS2022GRH.Coefficient333
open Real ChenThresholdGRH DecompC169a

/-- The coefficient at s equal to three is positive for C2 at most 114.
This is a scalar consequence of the selected table bound and epsilon guard.
Journal p. 1229. -/
theorem coefficient_at_three_pos (ε C₂ : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 63)
    (hC0 : 0 ≤ C₂) (hC1 : C₂ ≤ 114) :
    0 < 2 * exp eulerMascheroniConstant * log (3 - 1) / 3 -
      ε * C₂ * exp 2 * hS 3 := by
  have heg : (3 / 2 : ℝ) < exp eulerMascheroniConstant := by
    linarith [one_half_lt_eulerMascheroniConstant, add_one_le_exp eulerMascheroniConstant]
  have hl : (69 / 100 : ℝ) < log 2 := by linarith [log_two_gt_d9]
  have hf : (69 / 100 : ℝ) < 2 * exp eulerMascheroniConstant * log 2 / 3 := by
    nlinarith [mul_pos (sub_pos.mpr heg) (sub_pos.mpr hl)]
  have he : exp (-1 : ℝ) ≤ 3 / 8 := by
    have heq : exp (-1 : ℝ) * exp 1 = 1 := by rw [← exp_add]; norm_num
    have he1 : (8 / 3 : ℝ) < exp 1 := by linarith [exp_one_gt_d9]
    nlinarith [exp_pos (-1)]
  have hεC : ε * C₂ ≤ (1 / 63 : ℝ) * 114 :=
    mul_le_mul hε1 hC1 hC0 (by norm_num)
  have hεC0 : 0 ≤ ε * C₂ := mul_nonneg hε0 hC0
  have herr : ε * C₂ * exp (-1 : ℝ) ≤ ((1 / 63 : ℝ) * 114) * (3 / 8) :=
    mul_le_mul hεC he (exp_pos _).le (by norm_num)
  have hh : exp 2 * hS 3 = exp (-1 : ℝ) := by
    norm_num [hS]
    rw [← exp_add]
    norm_num
  norm_num only at ⊢
  rw [mul_assoc (ε * C₂), hh]
  norm_num at hf ⊢
  linarith

/-- The lower coefficient stays positive throughout the alpha range for C2 at most 114.
Journal p. 1229 and the selected row of Table 1 p. 1218.
The original leaf still permits arbitrary nonnegative C2. -/
theorem lowerCoefficient_pos_of_table_bound (α ε C₂ : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1 / 8)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 63) (hC0 : 0 ≤ C₂) (hC1 : C₂ ≤ 114) :
    0 < lowerCoefficient α ε C₂ := by
  have h0 := coefficient_at_three_pos ε C₂ hε0 hε1 hC0 hC1
  have hmono := lower_sieve_coefficient_strict 3 (4 - 8 * α) ε C₂
    (by norm_num) (by linarith) (by linarith) hε0 hC0
  rw [lower_coefficient_at_parameter α ε C₂ hα1] at hmono
  exact h0.trans hmono

end LeanLab.BS2022GRH.Coefficient333

#print axioms LeanLab.BS2022GRH.Coefficient333.coefficient_at_three_pos
#print axioms LeanLab.BS2022GRH.Coefficient333.lowerCoefficient_pos_of_table_bound
