import Mathlib

/-!
A cited specification for Theorem 1.3 on a provider of scaled zero multisets.
Z q H must be interpreted as the complete zero multiset in the paper's window.
No identification with actual Dirichlet L zeroes is proved here.
Source: Zhao 2025, displays 1.13 and 1.14, page 3.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- The weight in display 1.14, with multiplicity retained by Multiset. -/
noncomputable def weightFive (z : Multiset ℝ) : ℝ :=
  (z.map fun l => Real.exp (-(5 * l))).sum

/-- STATED and cited. The gap depends on c0, while the threshold also depends on H. -/
def PaperTheorem13 (Z : ℕ → ℝ → Multiset ℝ) : Prop :=
  ∀ c0 : ℝ, 0 < c0 → ∃ c1 : ℝ, 0 < c1 ∧
    ∀ H : ℝ, 1 ≤ H → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
      (∀ l ∈ Z q H, c0 ≤ l) → weightFive (Z q H) ≤ 1 - c1

/-- The cited specification is satisfiable on empty abstract zero data. -/
theorem theorem13_empty : PaperTheorem13 (fun _ _ => 0) := by
  intro c0 hc0
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro H hH
  refine ⟨1, ?_⟩
  intro q hq hq1 hmin
  norm_num [weightFive]

#print axioms theorem13_empty

end LeanLab.Zhao2025.Task56
