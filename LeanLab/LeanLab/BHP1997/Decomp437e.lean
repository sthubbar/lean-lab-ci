/-
P0069, pages 12 and 13, the dominant square moment for Case 1.
The cited mean square, cited large values and energy estimates remain premises.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp437d

namespace LeanLab.BHP1997.Decomp437e
open Classical Complex Thm4 MeanSquareC165 DecompC165c Decomp414a Decomp437c Decomp437d
open scoped BigOperators

/-- Pages 12 and 13, displays 3.11 and 3.12, summed on the dominant values.
The low character-time range uses the mean square estimate directly.
The other range uses the actual dyadic cells and their logarithmic count.
CONDITIONAL on the three explicit analytic premises. No cited sorry is called. -/
theorem dominant_square_moment (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 →
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
    ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a : ℕ → ℂ, CoeffBound a B →
    2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    (∀ p ∈ S, dominanceFlag ((q : ℝ) * T) F (dirPoly a c1 c2 F p.2 (half p.1)) = true) →
    (∑ p ∈ S, ‖dirPoly a c1 c2 F p.2 (half p.1)‖ ^ 2) ≤
      C * F * Real.log x ^ D := by
  exact Decomp414a.dominant_square_moment hmean hlarge henergy

end LeanLab.BHP1997.Decomp437e
