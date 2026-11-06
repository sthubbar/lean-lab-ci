/-
A check of the approximation reset used before P0013 page 70.
This concerns the reset inference from MinorHyp, not the three analytic inequalities.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119
import LeanLab.HelfgottArcs.MinorQAMGM

namespace LeanLab.HelfgottArcs.Decomp119

/-- The first approximation can have denominator equal to Q at the main threshold.
Source: P0013 page 3 and page 70, a derived parameter instance. -/
theorem first_approximation_endpoint325 :
    MinorHyp 2.16e20 (1 / 54000000000000) 1 27000000000000 0 ∧
      (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / 6 < (27000000000000 : ℝ) := by
  have h1 := MinorQAMGM.x0_cbrt
  have h2 : (2.16e20 : ℝ) ^ ((2 : ℝ) / 3) = (6e6 : ℝ) ^ (2 : ℕ) := by
    calc
      _ = ((2.16e20 : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        norm_num
      _ = _ := by rw [h1]
  constructor
  · norm_num [MinorHyp, h2]
  · rw [h1]; norm_num

/-- A valid reset approximation need not satisfy the strict page 70 disjunction.
Source: P0013 page 70, a negative test of the inference from the sealed MinorHyp.
The reset has numerator zero, denominator one and delta equal to eight million. -/
theorem reset_disjunction_counterexample325 :
    2 * (1 / 54000000000000 : ℝ) = 0 / 1 + 8000000 / 2.16e20 ∧
      (1 : ℝ) ≤ (2.16e20 : ℝ) ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6) ∧
      |(8000000 : ℝ) / 2.16e20| ≤
        1 / ((1 : ℝ) * ((2.16e20 : ℝ) ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))) ∧
      ¬ ((2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / 6 < 1 ∨
        8 * ((2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / 6) < |(8000000 : ℝ) * 1|) := by
  have h1 := MinorQAMGM.x0_cbrt
  have h2 : (2.16e20 : ℝ) ^ ((2 : ℝ) / 3) = (6e6 : ℝ) ^ (2 : ℕ) := by
    calc
      _ = ((2.16e20 : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        norm_num
      _ = _ := by rw [h1]
  have hs0 : 0 < Real.sqrt (6 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (2 : ℝ) ≤ Real.sqrt 6 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hs3 : Real.sqrt (6 : ℝ) ≤ 3 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · rw [h2, le_div_iff₀ (by positivity)]
    norm_num
    linarith
  · rw [h2, one_mul, one_div_div]
    norm_num
    linarith
  · rw [h1]
    norm_num

/-- The product of the second parameter choices has its exact two thirds scale.
Source: P0013 page 70, the displayed choices of U and V. -/
theorem parameter_product325 (x : ℝ) (hx : 0 < x) :
    U x * V x = (500 * Real.sqrt 6 / 3) * x ^ ((2 : ℝ) / 3) := by
  have hh : x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) = x ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add hx]
    congr 1
    norm_num
  unfold U V
  calc
    _ = (500 * Real.sqrt 6 / 3) *
        (x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 3)) := by ring
    _ = _ := by rw [hh]

/-- The Type I coefficient range extends beyond the short approximation block.
Source: P0013 page 70 and pages 10 to 13, a derived comparison. -/
theorem parameter_product_exceeds_short_range325 (x : ℝ) (hx : 0 < x) :
    (3 / 4 * x ^ ((2 : ℝ) / 3)) / 2 < U x * V x := by
  rw [parameter_product325 x hx]
  have hs : (2 : ℝ) < Real.sqrt 6 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hp : 0 < x ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hx _
  nlinarith

/-- The concrete first denominator cannot be retained under the reset Q bound.
Source: P0013 page 70, a parameter inference test. -/
theorem first_denominator_exceeds_reset325 :
    (2.16e20 : ℝ) ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6) < 27000000000000 := by
  have h1 := MinorQAMGM.x0_cbrt
  have h2 : (2.16e20 : ℝ) ^ ((2 : ℝ) / 3) = (6e6 : ℝ) ^ (2 : ℕ) := by
    calc
      _ = ((2.16e20 : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        norm_num
      _ = _ := by rw [h1]
  have hs : (2 : ℝ) < Real.sqrt 6 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  rw [h2, div_lt_iff₀ (by positivity)]
  norm_num
  linarith

end LeanLab.HelfgottArcs.Decomp119
