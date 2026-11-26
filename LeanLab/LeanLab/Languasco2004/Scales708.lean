/-
Jia 1996 pages 262 and 279, Lemma 21 and the Omega4 model.
Source https://doi.org/10.4064/aa-77-3-207-287.
Fixed positive power domains for the integer rough count input.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
namespace LeanLab.Languasco2004.Scales708
open Real

/-- Page 279 support: the cofactor and the cutoff stay in fixed power ranges
on the selected Omega4 domain. This is arithmetic support for Lemma 21. -/
theorem region4_power_scales (Y p q : ℝ) (hY : 1 < Y) (hq : 0 < q)
    (hqp : q ≤ p) (hp : p ≤ Y ^ (8 / 33 : ℝ))
    (hpq : Y ^ (41 / 90 : ℝ) < p * q) :
    Y ^ (17 / 33 : ℝ) ≤ Y / (p * q) ∧
      Y / (p * q) < Y ^ (49 / 90 : ℝ) ∧
      Y ^ (211 / 990 : ℝ) < q := by
  have hY0 : 0 < Y := lt_trans zero_lt_one hY
  have hp0 : 0 < p := hq.trans_le hqp
  have hpq0 : 0 < p * q := mul_pos hp0 hq
  have hcap : p * q ≤ Y ^ (16 / 33 : ℝ) := by
    calc p * q ≤ Y ^ (8 / 33 : ℝ) * Y ^ (8 / 33 : ℝ) :=
        mul_le_mul hp (hqp.trans hp) hq.le (Real.rpow_pos_of_pos hY0 _).le
      _ = Y ^ (16 / 33 : ℝ) := by rw [← Real.rpow_add hY0]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · apply (le_div_iff₀ hpq0).mpr
    calc Y ^ (17 / 33 : ℝ) * (p * q) ≤
        Y ^ (17 / 33 : ℝ) * Y ^ (16 / 33 : ℝ) :=
          mul_le_mul_of_nonneg_left hcap (Real.rpow_pos_of_pos hY0 _).le
      _ = Y := by rw [← Real.rpow_add hY0]; norm_num
  · apply (div_lt_iff₀ hpq0).mpr
    calc Y = Y ^ (49 / 90 : ℝ) * Y ^ (41 / 90 : ℝ) := by
          rw [← Real.rpow_add hY0]; norm_num
      _ < Y ^ (49 / 90 : ℝ) * (p * q) :=
        mul_lt_mul_of_pos_left hpq (Real.rpow_pos_of_pos hY0 _)
  · apply (mul_lt_mul_iff_left₀ (Real.rpow_pos_of_pos hY0 (8 / 33 : ℝ))).mp
    calc Y ^ (211 / 990 : ℝ) * Y ^ (8 / 33 : ℝ) = Y ^ (41 / 90 : ℝ) := by
          rw [← Real.rpow_add hY0]; norm_num
      _ < p * q := hpq
      _ ≤ Y ^ (8 / 33 : ℝ) * q := mul_le_mul_of_nonneg_right hp hq.le
      _ = q * Y ^ (8 / 33 : ℝ) := mul_comm _ _

#print axioms region4_power_scales
end LeanLab.Languasco2004.Scales708
