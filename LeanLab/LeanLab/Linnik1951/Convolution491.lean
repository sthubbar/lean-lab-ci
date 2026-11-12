/-
P0093 pages 161, 165 and 166. Sealed convolution and major assembly moved to avoid an import cycle.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT1622_major
import LeanLab.Linnik1951.Decomp487c

namespace LeanLab.Linnik1951

/-- LEAF. P0093 page 161 sentence after equation 6.3, in the printed relative form.
The elementary estimate of the convolution. No primes, no GRH. For n at most 3 the
sum is empty and the estimate is the choice of B. -/
theorem log_convolution_estimate1622 :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n →
      |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
        B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  exact log_convolution_estimate487

/-- P0093 page 165 equation 8.1 and page 166 equation 8.2. Exact
major_expansion_remainder376 statement. CONDITIONAL on GRH, MellinBound280
and the four analytic leaves in Decomp491b. -/
theorem major_expansion_recut1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        A * majorRelative376 k N +
          A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by
  obtain ⟨B, hB, N0, hL⟩ := arc_local_expansion1622 hG hM
  obtain ⟨B', hB', hC⟩ := log_convolution_estimate1622
  exact major_bookkeeping1622 k hk B hB N0 hL B' hB' hC

end LeanLab.Linnik1951
