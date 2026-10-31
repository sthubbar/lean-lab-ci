/-
AI wrote this Lean code for CODEX task58.
Certified outer reciprocal approximations for the two nested integrals.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58NestedBasis

open Real Finset intervalIntegral MeasureTheory

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

def j1WeightPoly (w : ℝ) : ℝ := (2 / 7) * geomPoly 10 (-(2 * w - 1) / 7)

def j2WeightPoly (w : ℝ) : ℝ := (1 / 5) *
  ((2 / 3) * geomPoly 20 ((2 * w - 1) / 3) + j1WeightPoly w)

theorem evalTerms_geometric (n : ℕ) (c r : ℚ) (z : ℝ) :
    evalTerms ((List.range n).map (fun j => (c * r ^ j, j))) z =
      (c : ℝ) * geomPoly n ((r : ℝ) * z) := by
  rw [evalTerms_range]
  unfold geomPoly
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  push_cast
  rw [mul_pow]
  ring

theorem j1WeightTerms_eval (z : ℝ) :
    evalTerms j1WeightTerms z = j1WeightPoly (z + 1 / 2) := by
  unfold j1WeightTerms
  rw [evalTerms_geometric]
  unfold j1WeightPoly
  push_cast
  congr 2
  ring

theorem j2WeightTerms_eval (z : ℝ) :
    evalTerms j2WeightTerms z = j2WeightPoly (z + 1 / 2) := by
  unfold j2WeightTerms
  rw [evalTerms_append, evalTerms_geometric, evalTerms_geometric]
  unfold j2WeightPoly j1WeightPoly
  push_cast
  have h1 : (2 * (z + 1 / 2) - 1) / 3 = (2 / 3 : ℝ) * z := by ring
  have h2 : -(2 * (z + 1 / 2) - 1) / 7 = (-2 / 7 : ℝ) * z := by ring
  rw [h1, h2]
  ring

theorem j1WeightPoly_error {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |j1WeightPoly w - 1 / (3 + w)| ≤ (2 / 1000000000 : ℝ) := by
  have harg : |-(2 * w - 1) / 7| ≤ (1 / 7 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [hw.1, hw.2]
  have hp := geomPoly_error harg (by norm_num : (1 / 7 : ℝ) < 1) 10
  have he : 1 / (3 + w) = (2 / 7 : ℝ) * (1 / (1 - (-(2 * w - 1) / 7))) := by
    rw [mul_one_div]
    apply (div_eq_div_iff (by linarith [hw.1]) (by linarith [hw.1])).mpr
    ring
  rw [he]
  unfold j1WeightPoly
  rw [← mul_sub, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 7)]
  refine (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2 / 7)).trans ?_
  norm_num

theorem j2FirstWeight_error {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |(2 / 3) * geomPoly 20 ((2 * w - 1) / 3) - 1 / (2 - w)| ≤
      (3 / 10000000000 : ℝ) := by
  have harg : |(2 * w - 1) / 3| ≤ (1 / 3 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [hw.1, hw.2]
  have hp := geomPoly_error harg (by norm_num : (1 / 3 : ℝ) < 1) 20
  have he : 1 / (2 - w) = (2 / 3 : ℝ) * (1 / (1 - ((2 * w - 1) / 3))) := by
    rw [mul_one_div]
    apply (div_eq_div_iff (by linarith [hw.2]) (by linarith [hw.2])).mpr
    ring
  rw [he, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  refine (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2 / 3)).trans ?_
  norm_num

theorem j2Weight_partial_fraction {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    1 / ((2 - w) * (3 + w)) = (1 / 5 : ℝ) * (1 / (2 - w) + 1 / (3 + w)) := by
  have h1 : 2 - w ≠ 0 := by linarith [hw.2]
  have h2 : 3 + w ≠ 0 := by linarith [hw.1]
  field_simp
  <;> ring

theorem j2WeightPoly_error {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |j2WeightPoly w - 1 / ((2 - w) * (3 + w))| ≤ (1 / 1000000000 : ℝ) := by
  have h1 := j1WeightPoly_error hw
  have h2 := j2FirstWeight_error hw
  rw [j2Weight_partial_fraction hw]
  unfold j2WeightPoly
  have he : (1 / 5 : ℝ) * ((2 / 3) * geomPoly 20 ((2 * w - 1) / 3) + j1WeightPoly w) -
      (1 / 5) * (1 / (2 - w) + 1 / (3 + w)) = (1 / 5) *
      (((2 / 3) * geomPoly 20 ((2 * w - 1) / 3) - 1 / (2 - w)) +
        (j1WeightPoly w - 1 / (3 + w))) := by ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)]
  have htri := abs_add_le ((2 / 3) * geomPoly 20 ((2 * w - 1) / 3) - 1 / (2 - w))
    (j1WeightPoly w - 1 / (3 + w))
  linarith

theorem outer_reciprocal_bounds {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |1 / (3 + w)| ≤ (1 / 3 : ℝ) ∧
      |1 / ((2 - w) * (3 + w))| ≤ (1 / 4 : ℝ) := by
  have h1 : 0 < 3 + w := by linarith [hw.1]
  have h2 : 0 < 2 - w := by linarith [hw.2]
  have hprod : 4 ≤ (2 - w) * (3 + w) := by nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  constructor
  · rw [abs_of_pos (one_div_pos.mpr h1), div_le_iff₀ h1]
    linarith [hw.1]
  · rw [abs_of_pos (one_div_pos.mpr (mul_pos h2 h1)), div_le_iff₀ (mul_pos h2 h1)]
    linarith

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.evalTerms_geometric
#print axioms LeanLab.ChenPrimeExceptional.Task58.j1WeightTerms_eval
#print axioms LeanLab.ChenPrimeExceptional.Task58.j2WeightTerms_eval
#print axioms LeanLab.ChenPrimeExceptional.Task58.j1WeightPoly_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.j2FirstWeight_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.j2Weight_partial_fraction
#print axioms LeanLab.ChenPrimeExceptional.Task58.j2WeightPoly_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.outer_reciprocal_bounds
