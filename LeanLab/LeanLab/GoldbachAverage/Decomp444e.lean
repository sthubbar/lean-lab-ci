import LeanLab.GoldbachAverage.TruncatedRanges444
import LeanLab.GoldbachAverage.EndpointBounds239

/-!
BHMS, https://arxiv.org/abs/1704.06103v2 page 7 Lemma 4 and page 17 difference step.
A uniform single endpoint formula leaves only the classical unsmoothed explicit formula open.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp444e
open MeasureTheory Complex
open Decomp287d TruncatedRanges444

/-- LEAF. BHMS page 7 Lemma 4 at q one, with cutoff T equal to x and x at most u at most three x.
The source constant is retained and the uniform error is at most C log squared x.
This leaf concerns one endpoint and contains no increment subtraction or variance estimate. -/
theorem truncated_endpoint : ∃ A : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x u : ℝ,
    2 ≤ x → u ∈ Set.Icc x (3 * x) →
      ‖((Chebyshev.psi u - u : ℝ) : ℂ) + cutoffPrimitive x u - A‖ ≤ C * Real.log x ^ 2 := by
  apply EndpointBounds239.endpoint_bound_of_source_remainder
    (fun T u => ((Chebyshev.psi u - u : ℝ) : ℂ) + cutoffPrimitive T u)
  sorry

/-- BHMS page 17, subtract the two endpoint formulas and cancel their common constant.
CONDITIONAL ON truncated_endpoint. -/
theorem truncated_increment_assembled : ∃ C : ℝ, 0 ≤ C ∧ ∀ x h t : ℝ,
    2 ≤ x → 2 ≤ h → h ≤ x → t ∈ Set.Icc x (2 * x) →
      ‖((Chebyshev.psi (t + h) - Chebyshev.psi t - h : ℝ) : ℂ) +
        lowZeros x h t + highZeros x h t‖ ≤ C * Real.log x ^ 2 := by
  obtain ⟨A, C, hC, hE⟩ := truncated_endpoint
  refine ⟨2 * C, by positivity, ?_⟩
  intro x h t hx hh hhx ht
  have h1 := hE x (t + h) hx ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 := hE x t hx ⟨ht.1, by linarith [ht.2]⟩
  have hid : ((Chebyshev.psi (t + h) - Chebyshev.psi t - h : ℝ) : ℂ) +
        lowZeros x h t + highZeros x h t =
      (((Chebyshev.psi (t + h) - (t + h) : ℝ) : ℂ) + cutoffPrimitive x (t + h) - A) -
        (((Chebyshev.psi t - t : ℝ) : ℂ) + cutoffPrimitive x t - A) := by
    have hs := cutoff_difference x h t (by linarith) (by linarith)
    push_cast at *
    linear_combination -hs
  rw [hid]
  have hn := norm_sub_le
    (((Chebyshev.psi (t + h) - (t + h) : ℝ) : ℂ) + cutoffPrimitive x (t + h) - A)
    (((Chebyshev.psi t - t : ℝ) : ℂ) + cutoffPrimitive x t - A)
  nlinarith

end LeanLab.GoldbachAverage.Decomp444e
