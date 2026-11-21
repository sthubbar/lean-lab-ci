/-
Kumchev and Liu 2007, Sums of primes and squares of primes in short intervals, arXiv 0801.0130.
SPLIT of Task628.rough_block_bulk, BlockInputs628.lean, FREE-nv-step task2085.

The target is the bulk Lemma 3.4 input for the short blocks of page 7,
isolated by Eq33RouteD. The proof chains three steps:
1. The cited analytic hypothesis A2.3 of page 7, as verified on page 15
   after display 52 by Lemma 3.4 of page 11 (rough_a23_hyp_F2085).
2. A lower parameter margin showing the block lower bound eventually
   exceeds windowY to the power 2/3 plus epsilon over four (lower_margin_F2085).
3. An upper parameter margin converting the block upper bound into the
   windowY over log X to the A plus 2 form (upper_margin_F2085).

The assembly rough_block_bulk_F2085 proves the exact target statement from
these three leaves with no sorry of its own. Each leaf is strictly easier
than the target: the analytic leaf is a single integral estimate, the two
margin leaves are elementary real inequalities.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.BlockInputs628

namespace LeanLab.KumchevLiu2007.F2085

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Task628
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF. P0088 page 7 hypothesis A2.3 for the rough weight lambda_0,
as established on page 15 after display 52 by Lemma 3.4 of page 11.
For every positive A there are B0, and for B above B0, epsilon positive,
eta positive, constants C and threshold X0 such that for X above X0,
windowY X epsilon to the power 2/3 plus eta at most H at most windowY X epsilon
over log X to the A, and alpha outside the major arcs, the integral of the
squared norm of the rough short sum over the block from windowY/4 to windowY
is at most C times H squared over log X to the A. This is the analytic heart
of the paper's Lemma 3.4 applied to the two sums of display 52. -/
theorem rough_a23_hyp_F2085 : ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
    ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε / Real.log X ^ A →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        (∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF. The lower block length X to the 7/18 plus epsilon times
log X to the B to the minus 4 eventually exceeds windowY X epsilon
to the 2/3 plus epsilon over 4. The exponent gap absorbs the four
logarithmic powers. Parameter margin step, elementary real estimate. -/
theorem lower_margin_F2085 (B ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 7 / 18) :
    ∃ X1 : ℝ, 3 ≤ X1 ∧ ∀ X : ℝ, X1 ≤ X →
      windowY X ε ^ (2 / 3 + ε / 4) ≤
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) := by
  sorry

/-- LEAF. The upper block bound windowY X epsilon times log X to the B
to the minus 4 is at most windowY X epsilon over log X to the A plus 2
once 4 B is at least A plus 2. Parameter margin step, elementary real
inequality using the log power comparison. -/
theorem upper_margin_F2085 {X B A Y : ℝ} (hX : 3 ≤ X) (hY : 0 ≤ Y)
    (hAB : A + 2 ≤ 4 * B) :
    Y * (Real.log X ^ B) ^ (-4 : ℤ) ≤ Y / Real.log X ^ (A + 2) := by
  sorry

/-- Assembly. The exact statement of Task628.rough_block_bulk, proved from
the three leaves above with no sorry of its own. The proof picks B0 large
enough so that 4B is at least A plus 2, handles the epsilon at most 7/18
case via the analytic leaf and the two margin leaves, and the case epsilon
above 7/18 is vacuous because the block range is empty. -/
theorem rough_block_bulk_F2085 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        (∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ (A + 2) := by
  have hA2 : 0 < A + 2 := by linarith
  obtain ⟨B0, hB0, hb⟩ := rough_a23_hyp_F2085 (A + 2) hA2
  refine ⟨max B0 ((A + 2) / 4), hB0.trans_le (le_max_left _ _), ?_⟩
  intro B hB ε hε
  have hAB : A + 2 ≤ 4 * B := by
    have := le_trans (le_max_right B0 ((A + 2) / 4)) hB
    linarith
  by_cases hε7 : ε ≤ 7 / 18
  · obtain ⟨C, X0, hC, hX0, hk⟩ :=
      hb B ((le_max_left _ _).trans hB) ε hε hε7 (ε / 4) (by positivity)
    obtain ⟨X1, hX1, hm⟩ := lower_margin_F2085 B ε hε hε7
    refine ⟨C, max X0 X1, hC, hX0.trans (le_max_left _ _), ?_⟩
    intro X H hX hlo hhi α hα
    have hx0 : X0 ≤ X := (le_max_left _ _).trans hX
    have hx1 : X1 ≤ X := (le_max_right _ _).trans hX
    have hX3 : 3 ≤ X := hX1.trans hx1
    have hY : 0 ≤ windowY X ε := (Real.rpow_pos_of_pos (by linarith) _).le
    have hupper : H ≤ windowY X ε / Real.log X ^ (A + 2) :=
      hhi.trans (upper_margin_F2085 hX3 hY hAB)
    have hlower : windowY X ε ^ (2 / 3 + ε / 4) ≤ H := (hm X hx1).trans hlo
    exact hk X H hx0 hlower hupper α hα
  · refine ⟨1, 3, one_pos, by norm_num, ?_⟩
    intro X H hX hlo hhi α hα
    exfalso
    have hX1 : 1 < X := by linarith
    have hL : 0 < Real.log X := Real.log_pos hX1
    have hk : 0 < (Real.log X ^ B) ^ (-4 : ℤ) := zpow_pos (Real.rpow_pos_of_pos hL B) _
    have hlt : windowY X ε < X ^ (7 / 18 + ε) := by
      unfold windowY
      exact Real.rpow_lt_rpow_of_exponent_lt hX1 (by linarith)
    have := mul_lt_mul_of_pos_right hlt hk
    linarith

end LeanLab.KumchevLiu2007.F2085
