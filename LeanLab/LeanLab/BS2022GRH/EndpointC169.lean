/- AI wrote this Lean code for CODEX task169.
Endpoint guards for Theorems 5 and 6, journal pp. 1228 and 1231. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC164a

namespace LeanLab.BS2022GRH.EndpointC169
open Real Finset Classical ChenThresholdGRH DecompC164a

/-- Condition 19 forces log X2 above 3200 on the Theorem 5 alpha range. -/
theorem log_endpoint_gt (α A u X₂ : ℝ) (hα : 0 < α) (hα1 : α < 1 / 8)
    (hA : 0 < A) (hc : Cond19 α A u X₂) (hX : 4e18 ≤ X₂) :
    3200 < log X₂ := by
  have hX0 : 0 < X₂ := by linarith
  have hL1 : 1 ≤ log X₂ := by
    apply (le_log_iff_exp_le hX0).mpr
    linarith [exp_one_lt_d9]
  have hden : 1 ≤ log X₂ ^ (A + 1) := one_le_rpow hL1 (by linarith)
  have hnum : 0 ≤ X₂ ^ α := (rpow_pos_of_pos hX0 _).le
  have hdiv : X₂ ^ α / log X₂ ^ (A + 1) ≤ X₂ ^ α := div_le_self hnum hden
  have hexp : exp u ≤ exp (log X₂ * α) := by
    simpa only [rpow_def_of_pos hX0] using hc.2.1.trans hdiv
  have hu : u ≤ log X₂ * α := exp_le_exp.mp hexp
  have hmul := mul_lt_mul_of_pos_left hα1 (by linarith : 0 < log X₂)
  have hu400 := hc.2.2.1
  linarith

/-- The near-one density factor is positive once log X exceeds 3200. -/
theorem density_factor_pos (X : ℝ) (hX : 0 < X) (hL : 3200 ≤ log X) :
    0 < 1 - 0.62 * log X / X ^ (1 / 16 : ℝ) := by
  have hLp : 0 < log X := by linarith
  have he := pow_div_factorial_le_exp (x := log X / 16) (by positivity) 2
  norm_num [Nat.factorial] at he
  have hsq : 0 ≤ (log X - 3200) * log X := mul_nonneg (by linarith) hLp.le
  have hlt : 0.62 * log X < exp (log X / 16) := by nlinarith
  have hr : X ^ (1 / 16 : ℝ) = exp (log X / 16) := by
    rw [rpow_def_of_pos hX]
    congr 1
    ring
  rw [hr]
  have hd : 0.62 * log X / exp (log X / 16) < 1 := (div_lt_one (exp_pos _)).mpr hlt
  linarith

/-- The explicit qG coefficient is nonnegative on the endpoint range. -/
theorem qG_nonneg (X : ℝ) (hX : 0 < X) (hL : 2 ≤ log X) : 0 ≤ qG X := by
  have hLp : 0 < log X := by linarith
  have hll : 0 ≤ log (log X) := log_nonneg (by linarith)
  have hE : 1 ≤ exp (log X / 4) := one_le_exp (by linarith)
  have hE0 : 0 < exp (log X / 4) := exp_pos _
  have hg1 : 0 ≤ firstGroup (log X) := by unfold firstGroup; positivity
  have hg2 : 0 ≤ secondGroup (log X) := by unfold secondGroup; positivity
  have hg3 : 0 ≤ thirdGroup (log X) := by
    have he : exp (log X / 2) = exp (log X / 4) ^ 2 := by
      rw [pow_two, ← exp_add]
      congr 1
      ring
    unfold thirdGroup
    rw [he]
    have hrewrite : 939.260 / (exp (log X / 4) * log X) -
        237.934 / (exp (log X / 4) ^ 2 * log X) =
        (939.260 * exp (log X / 4) - 237.934) /
          (exp (log X / 4) ^ 2 * log X) := by
      field_simp
      <;> ring
    rw [hrewrite]
    apply div_nonneg _ (by positivity)
    linarith
  rw [qG_groups X hX]
  positivity

/-- The journal cG coefficient is nonnegative on the endpoint range. -/
theorem cGJ_nonneg (X : ℝ) (hX : 0 < X) (hL : 2 ≤ log X) : 0 ≤ cGJ X := by
  have hq := qG_nonneg X hX hL
  have hll : 0 ≤ log (log X) := log_nonneg (by linarith)
  unfold cGJ pGJ
  positivity

end LeanLab.BS2022GRH.EndpointC169

#print axioms LeanLab.BS2022GRH.EndpointC169.log_endpoint_gt
#print axioms LeanLab.BS2022GRH.EndpointC169.density_factor_pos
#print axioms LeanLab.BS2022GRH.EndpointC169.qG_nonneg
#print axioms LeanLab.BS2022GRH.EndpointC169.cGJ_nonneg
