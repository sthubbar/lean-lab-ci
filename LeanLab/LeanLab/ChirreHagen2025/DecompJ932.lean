import LeanLab.ChirreHagen2025.Additional122
import LeanLab.ChirreHagen2025.MeanSquare122
import LeanLab.ChirreHagen2025.Pointwise297

/-!
Decomposition of Lemma 2.3 from P0075.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ChirreHagen2025.DecompJ932

open MeasureTheory Additional122

/-- Derived envelope from P0075 pages 2 and 3, Lemma 2.1.
CONDITIONAL ON the Backlund input through Pointwise297. -/
theorem leaf_integrand_bound : RiemannHypothesis → ∀ t : ℝ, 10 ^ 4 ≤ t →
    ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I)‖ ^ 2
    ≤ 10 * t := by
  -- CONDITIONAL ON Decomp122b.backlund_reduction through Pointwise297.
  exact Pointwise297.leaf_integrand_bound

/-- LEAF sorry. P0075 pages 4 and 5. Integration step up to T. -/
theorem leaf_integration_step : RiemannHypothesis → ∀ T : ℝ, 4 * 10 ^ 13 ≤ T →
  (∫ t in (10 ^ 4 : ℝ)..T,
    ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I)‖ ^ 2)
    ≤ 0.8056 * T := by
  sorry

/-- P0075 Lemma 2.3, pages 4 and 5. Assembled from the leaf lemmas. -/
theorem lemma2_3_assembled : lemma2_3 := by
  intro hRH T hT
  exact leaf_integration_step hRH T hT

end LeanLab.ChirreHagen2025.DecompJ932
