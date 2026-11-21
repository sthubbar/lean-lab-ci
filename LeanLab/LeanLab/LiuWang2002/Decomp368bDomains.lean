import Mathlib.Tactic.NormNum

/-!
Task666 memory repair. Existing declarations are moved without changing their text.
Source Schoenfeld 1976 page 356 display 5.1 star, derived finite certificates.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368

/-- Each proper subrange has a concrete positive integer witness.
Derived nonempty domains for page 356, display 5.1 star. -/
theorem split_instances :
    (1000000 < (1000001 : ℕ) ∧ 1000001 ≤ 2000000) ∧
    (2000000 < (2000001 : ℕ) ∧ 2000001 ≤ 4000000) ∧
    (4000000 < (4000001 : ℕ) ∧ 4000001 ≤ 8000000) ∧
    (8000000 < (8000001 : ℕ) ∧ 8000001 ≤ 16000000) ∧
    (16000000 < (16000001 : ℕ) ∧ 16000001 ≤ 32000000) ∧
    (32000000 < (32000001 : ℕ) ∧ 32000001 ≤ 100000000) := by
  norm_num

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.split_instances
