import LeanLab.Zhao2025.PaperTheorem14
import Mathlib

/-!
Decomposition of PaperTheorem14.
Source: Zhao 2025, displays 1.15 and 1.16, page 3.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task292

open LeanLab.Zhao2025.Task56

/-- LEAF: Paper page 3. -/
theorem leaf1 (theta : ℝ) (hth : 5 ≤ theta) (epsilon : ℝ) (heps : 0 < epsilon) :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      0 < (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) := sorry

/-- LEAF: Paper page 3. -/
theorem leaf2 (theta : ℝ) (hth : 5 ≤ theta) (epsilon : ℝ) (heps : 0 < epsilon) :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
        (2 + epsilon) * (q : ℝ) ^ theta /
          ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) := sorry

/-- Main assembly for PaperTheorem14. -/
theorem PaperTheorem14_assembly : PaperTheorem14 := by
  intro theta hth epsilon heps
  obtain ⟨Q1, hQ1⟩ := leaf1 theta hth epsilon heps
  obtain ⟨Q2, hQ2⟩ := leaf2 theta hth epsilon heps
  use max Q1 Q2
  intro q hq hq1 a ha1 haq hcop
  constructor
  · exact hQ1 q (le_trans (le_max_left Q1 Q2) hq) hq1 a ha1 haq hcop
  · exact hQ2 q (le_trans (le_max_right Q1 Q2) hq) hq1 a ha1 haq hcop

end LeanLab.Zhao2025.Task292
