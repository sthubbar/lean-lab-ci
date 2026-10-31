import Mathlib

/-!
AI wrote this Lean code for CODEX task52.
This closes the elementary omitted zero estimate recorded in U1489TruncB.
The analytic citation itself is not discharged by this elementary inequality.
-/

namespace LeanLab.HardyLittlewood1923.Task52

lemma exp_sub_one_le_mul_exp (u : ℝ) : Real.exp u - 1 ≤ u * Real.exp u := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u)) (Real.exp_pos u).le
  rw [← Real.exp_add] at h
  simp only [neg_add_cancel, Real.exp_zero] at h
  nlinarith only [h]

lemma exceptional_pair_remainder {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    x ^ δ / δ ≤ 1 / δ + x ^ (1 / 4 : ℝ) * Real.log x := by
  have hx0 : 0 < x := by linarith
  have he : Real.exp (δ * Real.log x) = x ^ δ := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have h := exp_sub_one_le_mul_exp (δ * Real.log x)
  rw [he] at h
  have hp : x ^ δ ≤ x ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hδ1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hb : x ^ δ - 1 ≤ δ * (x ^ (1 / 4 : ℝ) * Real.log x) := by
    calc _ ≤ (δ * Real.log x) * x ^ δ := h
      _ ≤ (δ * Real.log x) * x ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hδ.le hl)
      _ = _ := by ring
  rw [div_le_iff₀ hδ]
  have hd : (1 / δ + x ^ (1 / 4 : ℝ) * Real.log x) * δ =
      1 + δ * (x ^ (1 / 4 : ℝ) * Real.log x) := by
    field_simp
  rw [hd]
  linarith only [hb]

#print axioms exp_sub_one_le_mul_exp
#print axioms exceptional_pair_remainder

end LeanLab.HardyLittlewood1923.Task52
