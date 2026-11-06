/-
P0059 arXiv 1407.7902v1 page 7 display 2.44, audit for U-1626.
This module keeps the printed S5 verbatim, states the exact gap to the repaired zeroS5,
and checks that the changed conjunct of Lemma 2.5 is not vacuous at m = 2, X = exp 38.
Nothing here refutes display 2.49: under RH that sum is empty.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroBounds259

namespace LeanLab.KadiriLumley2014.Task259

/-- Display 2.44 exactly as printed on page 7, with R0 over 2 log X0. Not used by any assembly. -/
noncomputable def zeroS5Printed (X : ℝ) (m : ℕ) (c1 c2 c3 : ℝ) : ℝ :=
  (c1 + c2 * Real.log 30610000000 / 30610000000 + c3 / 30610000000 +
    (c1 + c2 / 30610000000) * 5.69693 / (2 * Real.log X) *
      (Real.log 30610000000) ^ 2 /
        (((m : ℝ) * 5.69693 / Real.log X) * (Real.log 30610000000) ^ 2 - 1)) /
    30610000000 ^ m

/-- The repaired S5 exceeds the print by exactly its printed second term. -/
theorem zeroS5_sub_printed (X : ℝ) (m : ℕ) (c1 c2 c3 : ℝ) :
    zeroS5 X m c1 c2 c3 - zeroS5Printed X m c1 c2 c3 =
      (c1 + c2 / 30610000000) * 5.69693 / (2 * Real.log X) *
        (Real.log 30610000000) ^ 2 /
          (((m : ℝ) * 5.69693 / Real.log X) * (Real.log 30610000000) ^ 2 - 1) /
        30610000000 ^ m := by
  unfold zeroS5 zeroS5Printed
  ring

/-- A crude lower bound for log H, used by the instances below. -/
theorem four_le_log_height : (4 : ℝ) ≤ Real.log 30610000000 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h]
  calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    _ ≤ 30610000000 := by norm_num

/-- Vacuity instance for the changed conjunct: at m = 2 and X = exp 38 the hypothesis hlog
holds and the denominator of the repaired term is positive. -/
theorem zeroS5_domain_instance :
    Real.log (Real.exp 38) < 5.69693 * ((2 : ℕ) : ℝ) * (Real.log 30610000000) ^ 2 ∧
      0 < (((2 : ℕ) : ℝ) * 5.69693 / Real.log (Real.exp 38)) *
        (Real.log 30610000000) ^ 2 - 1 := by
  have hL := four_le_log_height
  have hL2 : (16 : ℝ) ≤ (Real.log 30610000000) ^ 2 := by nlinarith
  rw [Real.log_exp]
  push_cast
  constructor <;> nlinarith

/-- At that instance the change is strict, so the repaired statement differs from the print. -/
theorem printed_lt_zeroS5 {c1 c2 : ℝ} (c3 : ℝ) (hc1 : 0 < c1) (hc2 : 0 ≤ c2) :
    zeroS5Printed (Real.exp 38) 2 c1 c2 c3 < zeroS5 (Real.exp 38) 2 c1 c2 c3 := by
  have hgap := zeroS5_sub_printed (Real.exp 38) 2 c1 c2 c3
  have hd := zeroS5_domain_instance.2
  have hL := four_le_log_height
  have hlogX : 0 < Real.log (Real.exp 38) := by
    rw [Real.log_exp]
    norm_num
  have hpos : 0 < (c1 + c2 / 30610000000) * 5.69693 / (2 * Real.log (Real.exp 38)) *
      (Real.log 30610000000) ^ 2 /
        ((((2 : ℕ) : ℝ) * 5.69693 / Real.log (Real.exp 38)) * (Real.log 30610000000) ^ 2 - 1) /
      30610000000 ^ 2 := by
    refine div_pos (div_pos (mul_pos (div_pos (mul_pos
      (add_pos_of_pos_of_nonneg hc1 (div_nonneg hc2 (by norm_num))) (by norm_num))
      (by linarith)) (pow_pos (by linarith) 2)) hd) (by norm_num)
  linarith

end LeanLab.KadiriLumley2014.Task259

#print axioms LeanLab.KadiriLumley2014.Task259.zeroS5_sub_printed
#print axioms LeanLab.KadiriLumley2014.Task259.four_le_log_height
#print axioms LeanLab.KadiriLumley2014.Task259.zeroS5_domain_instance
#print axioms LeanLab.KadiriLumley2014.Task259.printed_lt_zeroS5
