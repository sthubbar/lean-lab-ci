import LeanLab.Zhao2025.SmallCaseCutoff

/-!
Named analytic inputs for the entire small lambda range.
Display 4.5 is not an input. It is derived from these inputs in SmallCaseBound.
Source: Zhao 2025, displays 4.1, 4.3 and 4.4, pages 13 and 14.
Identification of the auxiliary T values with actual zero sums remains conditional.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56

/-- CONDITIONAL input: residual support 4.1, individual tails 4.3 and total tail 4.4. -/
def SmallCaseZeroEstimates (n : ℕ) (l : ℝ) (S : ℕ → ℝ) : Prop :=
  ∃ T : ℕ → ℝ,
    (∀ i ∈ Finset.range (n + 1), 0 ≤ T i) ∧
    (∀ i ∈ Finset.range (n + 1), T i ≤ 100 * Real.exp (-2.22 * smallCaseCutoff l)) ∧
    (∑ i ∈ Finset.range (n + 1), T i) ≤ 0.02 ∧
    S 0 = (Real.exp (-(10 / 3 * l)) - Real.exp (-(10 / 3 * smallCaseCutoff l))) + T 0 ∧
    ∀ i < n, S (i + 1) = T (i + 1)

end LeanLab.Zhao2025.Task56
