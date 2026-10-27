/-
AI wrote this Lean code for CODEX task58.
Algebra of the two sieve normalizations on P0039 pages 66 to 67.
No asymptotic sieve theorem is asserted here.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.U1435C0

open Real

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- The standard linear sieve value F of 3 used in the lab model. -/
def standardF3 : ℝ := 2 * exp eulerMascheroniConstant / 3

/-- Replacing the inverse product to N to the 1/6 by the one to N to the 1/10
scales the standard value by the Mertens exponent ratio in the limit model. -/
def page66F3Model : ℝ := (3 / 5) * standardF3

/-- Exact normalization algebra before any asymptotic input is used. -/
theorem normalization_change {A B S : ℝ} (hB : B ≠ 0) :
    A * S = (A / B) * (B * S) := by field_simp

/-- The exponent ratio between the two sifting cutoffs. -/
theorem normalization_ratio : ((1 : ℝ) / 10) / (1 / 6) = 3 / 5 := by norm_num

/-- The standard value is strictly positive. -/
theorem standardF3_pos : 0 < standardF3 := by
  unfold standardF3
  positivity

/-- The page 66 normalization model differs strictly from the standard F of 3. -/
theorem page66F3Model_lt : page66F3Model < standardF3 := by
  unfold page66F3Model
  nlinarith [standardF3_pos]

/-- Counting the factor 3/5 twice differs from counting it once. -/
theorem normalization_once_twice :
    (3 / 5 : ℝ) * page66F3Model = (9 / 25 : ℝ) * standardF3 ∧
      (3 / 5 : ℝ) * page66F3Model < (3 / 5 : ℝ) * standardF3 := by
  unfold page66F3Model
  constructor
  · ring
  · nlinarith [standardF3_pos]

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.normalization_change
#print axioms LeanLab.ChenPrimeExceptional.Task58.normalization_ratio
#print axioms LeanLab.ChenPrimeExceptional.Task58.standardF3_pos
#print axioms LeanLab.ChenPrimeExceptional.Task58.page66F3Model_lt
#print axioms LeanLab.ChenPrimeExceptional.Task58.normalization_once_twice
