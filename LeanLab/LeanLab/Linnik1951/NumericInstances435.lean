/-
P0093 page 165 after equation 7.19. An explicit entropy fraction.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Entropy435
import LeanLab.Linnik1951.Instances412

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 165 the small entropy exponent choice after 7.19.
The explicit fraction two to negative twenty has entropy cost below
one two hundredth times log two. This is a parameter consequence,
not a constant printed in the paper. -/
theorem entropy_cost_explicit435 :
    (1 / 1048576 : ℝ) * Real.log (Real.exp 1 / (1 / 1048576 : ℝ)) ≤
      (1 / 200 : ℝ) * Real.log 2 := by
  have he : Real.exp 1 / (1 / 1048576 : ℝ) = Real.exp 1 * (2 : ℝ) ^ 20 := by
    norm_num
    ring
  rw [he, Real.log_mul (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ^ 20 ≠ 0),
    Real.log_exp, Real.log_pow]
  nlinarith [Real.log_two_gt_d9]

/-- P0093 page 165 measure conclusion after 7.19. At radius one
sixteenth and exceptional fraction two to negative twenty, the one
period concentration set has measure at most four times two to M
times one two hundredth minus one for every M at least two. -/
theorem binary_unit_explicit_fraction435 (M : ℕ) (hM : 2 ≤ M) :
    volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
      (1 - (1 / 1048576 : ℝ)) * (M : ℝ) ≤ (nearIntegerIndices412 M 4 α).card} ≤
        ENNReal.ofReal (4 * (2 : ℝ) ^ ((M : ℝ) * ((1 / 200 : ℝ) - 1))) := by
  exact entropy_unit_bound435 M 4 hM le_rfl (1 / 1048576) (1 / 200)
    (by norm_num) (by norm_num) entropy_cost_explicit435

/-- P0093 page 165 measure conclusion after 7.19. The same explicit
fraction and radius give the three period real measure bound with
constant twelve. The concentration set has positive measure for every
finite M by binary_set_positive_measure412. -/
theorem binary_three_period_explicit435 (M : ℕ) (hM : 2 ≤ M) :
    volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - (1 / 1048576 : ℝ)) * (M : ℝ) ≤ (nearIntegerIndices412 M 4 α).card} ≤
        12 * (2 : ℝ) ^ ((M : ℝ) * ((1 / 200 : ℝ) - 1)) := by
  have hu := binary_unit_explicit_fraction435 M hM
  have ht := (entropy_three_periods435 M 4 (1 / 1048576)).trans (mul_le_mul' le_rfl hu)
  have he : (3 : ENNReal) * ENNReal.ofReal (4 * (2 : ℝ) ^ ((M : ℝ) * ((1 / 200 : ℝ) - 1))) =
      ENNReal.ofReal (12 * (2 : ℝ) ^ ((M : ℝ) * ((1 / 200 : ℝ) - 1))) := by
    rw [show (3 : ENNReal) = ENNReal.ofReal 3 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [he] at ht
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  exact hreal

end LeanLab.Linnik1951
