/- AI wrote this Lean code for CODEX task339. Goldbach is open.
The decreasing middle term of display 31 on journal p. 1240.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Bilinear339

namespace LeanLab.BS2022GRH.Mbar339
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- The elementary reciprocal plus linear function decreases below its turning point.
Auxiliary algebra for the middle term of journal display 31, p. 1240. -/
theorem reciprocal_linear_antitone (a b c : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcb : c * b ^ 2 ≤ 1) : 1 / b + c * b ≤ 1 / a + c * a := by
  have hb : 0 < b := ha.trans_le hab
  have hcab : c * a * b ≤ 1 := by
    calc c * a * b ≤ c * b * b := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hab hc) hb.le
      _ = c * b ^ 2 := by ring
      _ ≤ 1 := hcb
  have hp := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hcab)
  calc
    _ = (1 + c * b ^ 2) / b := by field_simp <;> ring
    _ ≤ (1 + c * a ^ 2) / a := (div_le_div_iff₀ hb ha).mpr (by nlinarith)
    _ = _ := by field_simp <;> ring

/-- The middle w term of mbar decreases through sqrt N over two.
The upper guard is the one explicitly stated after display 31 on p. 1240. -/
theorem middle_term_antitone (N u w : ℝ) (hN : 0 < N) (hu : 0 < u)
    (huw : u ≤ w) (hw : w ≤ √(N / 2)) :
    w ^ (-(1 / 2) : ℝ) + (2 * w / N) ^ (1 / 2 : ℝ) ≤
      u ^ (-(1 / 2) : ℝ) + (2 * u / N) ^ (1 / 2 : ℝ) := by
  have hw0 : 0 < w := hu.trans_le huw
  have hwsq : w ^ 2 ≤ N / 2 := (le_sqrt' hw0).mp hw
  have hc : 0 ≤ √(2 / N) := sqrt_nonneg _
  have hc2 : √(2 / N) ^ 2 = 2 / N := sq_sqrt (by positivity)
  have hcw : √(2 / N) * w ≤ 1 := by
    have hp : (√(2 / N) * w) ^ 2 ≤ 1 := by
      rw [mul_pow, hc2, div_mul_eq_mul_div]
      apply (div_le_iff₀ hN).mpr
      nlinarith
    nlinarith
  have hs := reciprocal_linear_antitone (√u) (√w) (√(2 / N))
    (sqrt_pos.mpr hu) (sqrt_le_sqrt huw) hc (by simpa only [sq_sqrt hw0.le] using hcw)
  have hid (v : ℝ) (hv : 0 < v) :
      v ^ (-(1 / 2) : ℝ) + (2 * v / N) ^ (1 / 2 : ℝ) =
        1 / √v + √(2 / N) * √v := by
    rw [rpow_neg hv.le, ← sqrt_eq_rpow]
    rw [show 2 * v / N = (2 / N) * v by ring, ← sqrt_eq_rpow,
      sqrt_mul (by positivity)]
    simp only [one_div]
  rw [hid w hw0, hid u hu]
  exact hs

end
end LeanLab.BS2022GRH.Mbar339
#print axioms LeanLab.BS2022GRH.Mbar339.reciprocal_linear_antitone
#print axioms LeanLab.BS2022GRH.Mbar339.middle_term_antitone
