/-
P0093 pages 160 and 161, equations 6.1 through 6.3. A record about the older split
SPLIT_principal_convolution491: under the extended Riemann hypothesis the size
bound claimed by its leaf principal_integral_amplitude491 is false. The witness is
modulus one and residual N for large N. It combines the principal convolution
estimate of Decomp491b with the incompatibility theorem of Decomp549a.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp549a

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- P0093 pages 160 and 161 equations 6.1 through 6.3. QUESTION about the split
SPLIT_principal_convolution491. Under the extended Riemann hypothesis and the
Mellin estimate, the conclusion of the leaf principal_integral_amplitude491, a
bound for the principal square integral alone by the two error sizes for every
residual up to N, is false. By principal_convolution491 the integral at modulus
one and residual N is close to the damped logarithmic convolution, which is
larger than the error sizes. So that leaf can hold only if one of its two
hypotheses fails. -/
theorem principal_amplitude_false491 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ¬ (∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
        ‖principalIntegral491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by
  intro hAmp
  obtain ⟨C, hC, N0, h⟩ := principal_convolution491 hG hM
  exact not_principal_amplitude_and_unit549
    ⟨hAmp, C, hC, N0, fun N hN q hq hqQ _ n _ hn => h N hN q hq hqQ n hn⟩

end LeanLab.Linnik1951
