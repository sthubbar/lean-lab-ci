/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 page 2 display 3, weaker variants.
The lab's existing certified twin prime constant bounds are reused without alteration.
-/
import LeanLab.PlattTrudgian2014.PaperInputs
import LeanLab.ChenExplicit.TwinCUpper

namespace LeanLab.PlattTrudgian2014

theorem paperC0_eq_twinC : paperC0 = LeanLab.ChenExplicit.twinC := rfl

theorem paperC0_weak_bounds : (0.65 : ℝ) ≤ paperC0 ∧ paperC0 ≤ 0.66017 := by
  rw [paperC0_eq_twinC]
  constructor
  · convert LeanLab.ChenExplicit.twinC_ge_065 using 1 <;> norm_num
  · convert LeanLab.ChenExplicit.TwinCUpper.twinC_le_066017 using 1 <;> norm_num

#print axioms paperC0_eq_twinC
#print axioms paperC0_weak_bounds

end LeanLab.PlattTrudgian2014
