/- SPLIT FREE-nv-minimax2 task2982: decomposition of Task628.rough_block_bulk.
Kumchev and Liu 2007, P0088, arXiv 0801.0130.

This file is a SPLIT of the CITED leaf Task628.rough_block_bulk. It introduces
LEAF lemmas (one open, one proved) and an assembly theorem rough_block_bulk_F2982
with no sorry, proved from the leaves via the existing conditional proof
rough_block_bulk_of_hyp.

The assembly statement matches Task628.rough_block_bulk character for character.
The lower block length loses four logarithmic powers relative to the final H
range; a positive epsilon margin absorbs that loss.

AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.KumchevLiu2007.BlockInputs628
import LeanLab.KumchevLiu2007.DQRoughBlockBulkDecisions
import LeanLab.KumchevLiu2007.Decomp556a

namespace LeanLab.KumchevLiu2007.Task2982

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Task628 DQRoughBlockBulk
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF. Page 7 hypothesis A2.3 for the rough weight lambda_0 = Phi(m, z0),
z0 = Y^(1/4) P^(-2), Y = X^(7/12 + eps/2), P = (log X)^B. The verification
uses the circle-method machinery; the lab splits it further in other files
which stay open. The H range loses four logarithmic powers relative to the
final range; a positive epsilon margin absorbs that loss. -/
theorem leaf_rough_a23_hyp : RoughA23Hyp := by sorry

/-- LEAF. Page 6 short block parameter consequence: when the block length H lies
between X^(7/18 + eps) P^(-4) and windowY X eps * P^(-4), epsilon is at most
7/18. This is a derived parameter step, not an analytic input. -/
theorem leaf_epsilon_upper_bound {X H B ε : ℝ} (hX : 3 ≤ X) (hB : 0 ≤ B)
    (hε : 0 < ε)
    (hlo : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H)
    (hhi : H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ)) :
    ε ≤ 7 / 18 := by
  have h := block_window_parameters hX hB hε hlo hhi
  exact h.1

/-- Assembly theorem. Exact statement of Task628.rough_block_bulk, proved from
the LEAFs with no sorry. The bulk estimate follows from the hypothesis leaf
leaf_rough_a23_hyp through the existing conditional proof
rough_block_bulk_of_hyp. -/
theorem rough_block_bulk_F2982 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        (∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ (A + 2) := by
  have h_rough : RoughA23Hyp := leaf_rough_a23_hyp
  exact rough_block_bulk_of_hyp h_rough A hA
