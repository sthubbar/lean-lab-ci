import LeanLab.Zhao2025.PackedZeros

/-!
The infinite outer sum of display 1.10 for finite zero families with empty padding.
The same positive gap works for every size, cutoff and labelled case.
The small case is CONDITIONAL ON SmallCaseZeroEstimates for 4.1, 4.3 and 4.4.
The later cases retain the legacy wrapper inputs.
Source: Zhao 2025, display 1.10, page 3, https://arxiv.org/abs/2511.05631v2.
This is CONDITIONAL ON those analytic inputs. It does not prove them for L functions.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- CONDITIONAL display 1.10, with summability and the nested exponential sums explicit. -/
theorem display110_tsum {ι : Type*} (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ (k : Fin 11) (n : ℕ) (l11 L : ℝ)
      (H B : ℕ → Finset ι) (lam : ι → ℝ),
      c0 ≤ l11 →
      CaseInputs k n l11 (fun i => residualSum (B i) lam L)
        (fun i => cappedSum (B i) lam L) (fun i => zeroSum (H i) lam) →
      Summable (fun i : ℕ =>
        (∑ j ∈ packedZeros k n H B i, Real.exp (-(10 / 3 * lam j))) ^ 2) ∧
      ∑' i : ℕ, (∑ j ∈ packedZeros k n H B i, Real.exp (-(10 / 3 * lam j))) ^ 2 ≤ 1 - c1 := by
  obtain ⟨c1, hc1, hall⟩ := display110_zero_sums (ι := ι) c0 hc0
  refine ⟨c1, hc1, ?_⟩
  intro k n l11 L H B lam hl h
  have hs := packed_square_sum k n H B lam
  refine ⟨hs.1, ?_⟩
  change ∑' i : ℕ, zeroSum (packedZeros k n H B i) lam ^ 2 ≤ 1 - c1
  rw [hs.2]
  exact hall k n l11 L H B lam hl h

#print axioms display110_tsum

end LeanLab.Zhao2025.Task56
