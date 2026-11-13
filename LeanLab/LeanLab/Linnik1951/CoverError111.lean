/-
P0093 Linnik 1951, pages 155 to 168, Sections 3 to 10. The three steps still
open in the burst 9 split of major_error_split111 and exceptional_error_split111.
AI wrote the Lean code. Binary Goldbach is open.

These three theorems are kept in their own file because Decomp111 must stay free
of new admissions: Decomp111 proves lemma4_measure_split111,
covered_square_split111 and major_truncated_split111 from them.

No definition is introduced here. Each statement writes out the definitions it
needs, so its terms are definitionally the ones Decomp111 builds from
largeSet111, coverSet111, arcContributionSplit111, majorArcsSplit111,
scale111 and mainTermTrunc111, and Decomp111 applies the leaves directly with no
transport lemma. The series, the major arcs, the arc contribution and the scale
are the _up111 copies already upstream in CircleSplit111, which are renamed
copies of the Split111 copies of Decomp111 in that order.
-/
import LeanLab.Linnik1951.CircleSplit111

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997
open Finset

/-- LEAF: P0093 page 162, Lemma 4, equation 7.6, used for 2 eta in the proof of
Lemma 5 on page 165: for every positive kappa there are a positive eta below one
half and a positive C so that, for all large N, the measure of the set of alpha
in the interval from minus 1 to 2 where the damping at zero is more than 1 minus
2 eta times the value at alpha is at most C times N to the kappa minus 1. The
paper proves it by the binary digit count 7.9 to 7.18. -/
theorem lemma4_measure_leaf111 (κ : ℝ) (hκ : 0 < κ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      MeasureTheory.volume {α : ℝ | α ∈ Set.Icc (-1 : ℝ) 2 ∧
        (1 - 2 * η) * ‖powerFourier111_up111 N 0‖ < ‖powerFourier111_up111 N α‖}
        ≤ ENNReal.ofReal (C * (N : ℝ) ^ (κ - 1)) := by
  sorry

/-- LEAF: P0093 page 166, Lemma 6, the GRH estimate 9.1 on the systems F_q with
q above Q, and the count in the proof of Lemma 7, equation 9.3, without the
factor T to the k: for any at most N to the 0.01 segments of length N to the
minus 0.99, the integral of the squared prime series over their minor arc part is
at most B N times N to the minus one twentieth. -/
theorem covered_square_leaf111 (hG : GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      ∀ s : Finset ℝ, (s.card : ℝ) ≤ (N : ℝ) ^ (1 / 100 : ℝ) →
        ∫ α in (⋃ c ∈ s, Set.Icc (c - 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ)))
              (c + 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ)))) ∩ (Set.Icc 0 1 \ majorArcs280_up111 N),
            ‖primeFourier111_up111 N α‖ ^ 2 ≤ B * N / (N : ℝ) ^ (1 / 20 : ℝ) := by
  sorry

/-- LEAF: P0093 Sections 3 to 6 with equation 6.4 on page 161, Section 8
equations 8.1 and 8.2 on page 165, and equation 10.7 on page 168. The major arc
integral equals the main term built from the truncated singular series at Q
equal to N to the one tenth, up to an error that is eventually below any epsilon
times the scale. -/
theorem major_truncated_leaf111 (hG : GRH) (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280_up111 k N (majorArcs280_up111 N) -
          (by classical exact
            ∑ ν ∈ (Finset.univ.filter fun ν : Fin k → Fin (N + 1) =>
                (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧
                  Even (N - ∑ i, 2 ^ (ν i).val)),
              (∑ q ∈ Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
                  ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
                    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
                      Real.cos (2 * Real.pi * ((N - ∑ i, 2 ^ (ν i).val : ℕ) : ℝ) *
                        (a : ℝ) / (q : ℝ))) *
                (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2)|
        ≤ ε * scale111_up111 k N := by
  sorry

end LeanLab.Linnik1951
