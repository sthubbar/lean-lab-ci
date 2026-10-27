/-
P0073 Stein and Stein 1965: the printed S-sequence examples, kernel checked.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import LeanLab.Stein1965.Statements

namespace LeanLab.Stein1965

/-- Page 428: the first 22 terms of `{b_i}_3` are as printed. MATCH. -/
theorem seq3_match : steinSeq 3 22 = printedSeq3 := by decide +kernel

/-- Page 428: the first 22 terms of `{b_i}_11` are as printed. MATCH. -/
theorem seq11_match : steinSeq 11 22 = printedSeq11 := by decide +kernel

/-- Page 428: the first 16 terms of `{b_i}_3` are a 2-basis for the even numbers `6 ≤ 2n ≤ 122`. -/
theorem first16_covers :
    ∀ n ∈ List.range 59, covered (printedSeq3.take 16) (2 * n + 6) = true := by decide +kernel

/-- Page 428: 124 is not a sum of two of the first 16 terms. -/
theorem first16_misses_124 : covered (printedSeq3.take 16) 124 = false := by decide +kernel

/-- Page 428: `124 = 101 + 23`, and 101 is the 17th term. -/
theorem p124 : (101 + 23 = 124) ∧ printedSeq3[16]! = 101 ∧ printedSeq3[5]! = 23 := by
  refine ⟨rfl, rfl, rfl⟩

/-- The prime 101 needed for 124 is the largest admissible `a`: `bestA` at 124 is 101. -/
theorem best124 : bestA 3 (printedSeq3.take 16) 124 = some 101 := by decide +kernel

/-- Backtracking, page 428: the sequence is not increasing, 109 and 113 come before 101. -/
theorem backtracking : printedSeq3[16]! < printedSeq3[15]! := by decide +kernel

end LeanLab.Stein1965
