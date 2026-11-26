import LeanLab.RieselVaughan1983.Parameter709

/-!
The two bounds in Schoenfeld 1976 page 345 equation 7.28.
The parameter family d at least one quarter includes the paper's logarithmic d.
These bounds do not estimate any zeta zero sum.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real

namespace LeanLab.RieselVaughan1983.Task709

/-- The two H bounds from equation 7.28, with the paper's d generalized. -/
theorem schoenfeldH_bounds (X d v : ℝ) (hX : 0 < X) (hd : 1 / 4 ≤ d)
    (hv : 0 < v) (hden : 1 < 2 * v ^ 2) (hv1 : v ≤ 1) :
    v ^ 6 * (2 * v ^ 2 - 1) < schoenfeldH X d v ∧
      schoenfeldH X d v < (v + d / X) ^ 2 := by
  let b : ℝ := d / X
  let a : ℝ := (1 + 2 * d) / (2 * X)
  let P : ℝ := v ^ 4 * (2 * v ^ 2 - 1)
  have hd0 : 0 < d := by linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hvb : 0 < v + b := by positivity
  have hva : 0 < v + a := by positivity
  have hab : b < a := by
    dsimp [a, b]
    apply (div_lt_div_iff₀ hX (by positivity : (0 : ℝ) < 2 * X)).mpr
    nlinarith
  have ha3 : a ≤ 3 * b := by
    dsimp [a, b]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * X) hX).mpr
    nlinarith [mul_nonneg (show 0 ≤ 4 * d - 1 by linarith) hX.le]
  have hdiff : 0 < 2 * v ^ 2 - 1 := by linarith
  have hP0 : 0 < P := by dsimp [P]; positivity
  have hv2 : v ^ 2 ≤ 1 := pow_le_one₀ hv.le hv1
  have hv4 : v ^ 4 ≤ 1 := pow_le_one₀ hv.le hv1
  have hP1 : P ≤ 1 := by
    dsimp [P]
    exact (mul_le_of_le_one_right (by positivity : 0 ≤ v ^ 4)
      (by nlinarith : 2 * v ^ 2 - 1 ≤ 1)).trans hv4
  have hratio : v ^ 2 < (v + b) ^ 3 / (v + a) := by
    apply (lt_div_iff₀ hva).mpr
    have hleft : v ^ 2 * (v + a) ≤ v ^ 2 * (v + 3 * b) := by gcongr
    have hright : v ^ 2 * (v + 3 * b) < (v + b) ^ 3 := by
      nlinarith [mul_pos hv (sq_pos_of_pos hb), pow_pos hb 3]
    exact hleft.trans_lt hright
  have hlower := mul_lt_mul_of_pos_left hratio hP0
  have hupper : P * (v + b) ^ 3 / (v + a) < (v + b) ^ 2 := by
    calc
      _ ≤ (v + b) ^ 3 / (v + a) := by
        apply div_le_div_of_nonneg_right _ hva.le
        exact mul_le_of_le_one_left (by positivity) hP1
      _ < (v + b) ^ 2 := by
        apply (div_lt_iff₀ hva).mpr
        have h := mul_lt_mul_of_pos_left hab (sq_pos_of_pos hvb)
        nlinarith only [h]
  constructor
  · dsimp [schoenfeldH]
    change v ^ 6 * (2 * v ^ 2 - 1) < P * (v + b) ^ 3 / (v + a)
    convert hlower using 1 <;> dsimp [P] <;> ring
  · exact hupper

end LeanLab.RieselVaughan1983.Task709
