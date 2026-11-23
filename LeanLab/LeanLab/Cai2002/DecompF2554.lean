/-
SPLIT of leaf118_sieve_three, FREE-nv-glm3 task2554.
Cai 2002 page 604 display 4.15. The all large triple region S3 is bounded by
0.1564 times the main scale C N * N^0.95 / log^2 N for all sufficiently large even N.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Decomp337c
import LeanLab.Cai2002.Decomp118

open Filter Asymptotics Finset Real intervalIntegral Set
open scoped Topology

namespace LeanLab.Cai2002

/-- LEAF. Page 604 display 4.15. S3 is bounded by the closed switched index cardinality.
For N at least 2, every all large triple counted by S3 has a unique representation
in the closed switched index. This is the finite combinatorial step before any
analytic estimate. -/
theorem leafF2554_s3_le_closed_card (N : ℕ) (hN : 2 ≤ N) :
    (S3 N 0.95 : ℝ) ≤ (((switchedClosedIndex337 N (switchedThreeE306 N)).filter
      (fun b => (N - b.1 * b.2).Prime)).card : ℝ) := by
  exact_mod_cast sieve_three_closed337 N hN

/-- LEAF. Page 604 display 4.15, the switching argument bound.
For large even N, the closed switched index cardinality is at most
(pair sum + 0.00001) times the main scale. This is the main analytic step
using Theorem 6, the Wu mean value theorem, and the finite switching losses. -/
theorem leafF2554_closed_card_le_main (δ : ℝ) (hδ : 0 < δ) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (((switchedClosedIndex337 N (switchedThreeE306 N)).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤
        (sieveThreePairSum337 N + δ) * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  exact leaf337_three_switching δ hδ

/-- LEAF. Page 604 display 4.15, the prime pair sum limit.
For large N, the weighted all large prime pair sum is at most the integral
coefficient plus an arbitrarily small delta. This is the second analytic step
connecting the pair sum to the integral constant. -/
theorem leafF2554_pair_sum_le_coeff (δ : ℝ) (hδ : 0 < δ) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      sieveThreePairSum337 N ≤ sieveThreeCoefficient337 + δ := by
  exact leaf337_three_pair_sum δ hδ

/-- LEAF. Page 604 display 4.15, the integral coefficient bound.
The exact integral coefficient 8/(2*0.95-1) times the integral from 2 to 2.29
is at most 0.1564. This is already proved as eq415_margin118 giving 0.15635. -/
theorem leafF2554_coeff_le_01564 :
    sieveThreeCoefficient337 ≤ 0.1564 := by
  have h := eq415_margin118
  unfold sieveThreeCoefficient337
  linarith

/-- Assembly of leaf118_sieve_three from the four leaves above.
The statement after the name is copied character for character from
leaf118_sieve_three in Decomp118.lean. -/
theorem leaf118_sieve_three_F2554 :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S3 N 0.95 : ℝ) ≤ 0.1564 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  obtain ⟨N0, h0⟩ := leafF2554_closed_card_le_main 0.00001 (by norm_num)
  obtain ⟨N1, h1⟩ := leafF2554_pair_sum_le_coeff 0.00001 (by norm_num)
  refine ⟨max 2 (max N0 N1), fun N he hN => ?_⟩
  have h2 : 2 ≤ N := (le_max_left ..).trans hN
  have h0N : N0 ≤ N := (le_max_left N0 N1).trans ((le_max_right ..).trans hN)
  have h1N : N1 ≤ N := (le_max_right N0 N1).trans ((le_max_right ..).trans hN)
  have hcard := leafF2554_s3_le_closed_card N h2
  have hmain := h0 N he h0N
  have hsum := h1 N h1N
  have hcoeff := leafF2554_coeff_le_01564
  have hpos : 0 ≤ C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2 :=
    (leaf118_scale_pos N h2).le
  calc
    (S3 N 0.95 : ℝ) ≤ (((switchedClosedIndex337 N (switchedThreeE306 N)).filter
      (fun b => (N - b.1 * b.2).Prime)).card : ℝ) := hcard
    _ ≤ (sieveThreePairSum337 N + 0.00001) * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := hmain
    _ ≤ ((sieveThreeCoefficient337 + 0.00001) + 0.00001) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
      gcongr
    _ = (sieveThreeCoefficient337 + 0.00002) * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by ring
    _ ≤ 0.1564 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
      gcongr
      linarith

end LeanLab.Cai2002
