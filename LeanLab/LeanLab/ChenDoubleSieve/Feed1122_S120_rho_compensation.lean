import LeanLab.ChenDoubleSieve.Decomp347j

/-!
The compensation leaf left after the finite transport of Wu 2004 equation 9.6.
Source: Wu 2004, https://arxiv.org/pdf/0705.1652, pages 35 and 36.
`leaf_eq96` in Feed1122_Decomp315a_first_half follows from `crossing_compensation_rho`
below, the proved `Task347.first_half_transport_identity` and the proved
`Task347.baseline_bound`. This leaf asks for less than equation 9.6 itself:
it has no D12, no base sieve count and no Upsilon 0 to 9 term.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315.Feed1122S120
open Task275 Task347
open Wu41 (S PS)

/-- LEAF: Wu 2004 page 36, the compensation in the proof of equation 9.6 after the S1
substitution is split at N to the rho, rho one quarter: the crossing defect of the sealed
Upsilon 10 convention is paid by the three nonnegative reserves, namely the crossing pairs
with N to the rho at most p two below N to the sigma two, the S3 raising surplus, and S4,
up to C times N to the eleven twelfths. The analogue at 9.7 is `crossing_compensation`;
its recorded QUESTION on the literal Upsilon 10 convention applies here too. Class HARD. -/
theorem crossing_compensation_rho : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      crossingDefect N ≤
        (((∑ q ∈ lowerCrossingPairs N, S (primeSequence N) (q.1 * q.2) N q.1) : ℝ) -
          ((∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧
              (p : ℝ) < (N : ℝ) ^ kappa2 ∧ (N : ℝ) ^ kappa2 ≤ q ∧
              (q : ℝ) < (N : ℝ) ^ (1 / 4 : ℝ)),
            S (primeSequence N) (q.1 * q.2) N q.1 : ℕ) : ℝ)) +
        (exemptUpsilon10 N + tripleTerms N 2 -
          (Wu08.S₃ (primeSequence N) N ((N : ℝ) ^ kappa2) ((N : ℝ) ^ sigma2) : ℝ)) +
        (Wu08.S₄ (primeSequence N) N ((N : ℝ) ^ kappa2) ((N : ℝ) ^ sigma2) : ℝ) +
        C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  sorry

end LeanLab.ChenDoubleSieve.Task315.Feed1122S120
