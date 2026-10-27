import LeanLab.Zhao2025.Display110Tsum

/-!
The repaired case bundle yields one positive uniform gap for a linked zero sum layout.
The small case is CONDITIONAL ON SmallCaseZeroEstimates for 4.1, 4.3 and 4.4.
The legacy wrapper alone does not cover tiny lambda.
The selected label only records the case and the size of its head block.
The infinite sequence has empty zero sets after the finite layout.
Source: Zhao 2025, display 1.10, page 3, and Section 4, pages 14 to 16.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6900

/-- CONDITIONAL display 1.10 from the repaired input bundle with its small case input named. -/
theorem display1_10_conditional {ι : Type*} (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ (n : ℕ) (l11 L : ℝ) (H B : ℕ → Finset ι) (lam : ι → ℝ),
      c0 ≤ l11 →
      (∃ k : Fin 11, CaseInputs k n l11 (fun i => residualSum (B i) lam L)
        (fun i => cappedSum (B i) lam L) (fun i => zeroSum (H i) lam)) →
      ∃ k : Fin 11,
        CaseInputs k n l11 (fun i => residualSum (B i) lam L)
          (fun i => cappedSum (B i) lam L) (fun i => zeroSum (H i) lam) ∧
        Summable (fun i : ℕ =>
          (∑ j ∈ packedZeros k n H B i, Real.exp (-(10 / 3 * lam j))) ^ 2) ∧
        ∑' i : ℕ, (∑ j ∈ packedZeros k n H B i, Real.exp (-(10 / 3 * lam j))) ^ 2 ≤ 1 - c1 := by
  obtain ⟨c1, hc1, hall⟩ := display110_tsum (ι := ι) c0 hc0
  refine ⟨c1, hc1, ?_⟩
  intro n l11 L H B lam hl h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk, hall k n l11 L H B lam hl hk⟩

#print axioms display1_10_conditional

end LeanLab.Zhao2025.Task56
