/-
Wiring units P1122-0129 and P1122-0132, burst-20261122, session S33. P0088,
Kumchev and Liu, arXiv 0801.0130, Theorem 1 on the written range of page 16,
the Prop Task129W.kumchev_liu_thm1_written, from the two Prep1121 assemblies:
the major arc block of DQMajorArcCharWiring and the rough block bulk of
Prep1121KLRoughBulk with its cuts in Prep1121DKLRoughCut.

rough_block_bulk_of_sums is the page 15 assembly after display 52 with the two
Lemma 3.4 applications as hypotheses; its proof is the proof of
Prep1121KLRough.rough_block_bulk_of_block_leaves with the two leaves replaced by
arguments, so the finer cuts first_sum_block_of_pieces and
second_sum_block_of_dyadic can feed it.

The Palomar headline thm1_written_of_char_inputs is CONDITIONAL ON A12Corr and
A22Corr only, with the open LEAF pieces beneath it. Task628.low_H_large_eps,
which P0088 never states, is not in its dependency closure, checked by a walk of
the constants its proof uses; that is unit P1122-0132. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.DQMajorArcCharWiring
import LeanLab.KumchevLiu2007.Prep1121DKLRoughCut

namespace LeanLab.KumchevLiu2007.DQThm1Char

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Eq33RouteD
open Prep1121KLRough Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 15 after display 52: the statement of Task628.rough_block_bulk from
page 11 Lemma 3.4 applied to the first and second sums of display 52, given as h1
and h2 in the exact form of the leaves first_sum_block and second_sum_block.
No sorry of its own. -/
theorem rough_block_bulk_of_sums
    (h1 : type_of% @Prep1121KLRough.first_sum_block)
    (h2 : type_of% @Prep1121KLRough.second_sum_block) (A : ℝ) (hA : 0 < A) :
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
  obtain ⟨B1, hB1, h1⟩ := h1 (A + 2) hA2
  obtain ⟨B2, hB2, h2⟩ := h2 (A + 2) hA2
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε => ?_⟩
  have hBpos : 0 < B := (lt_max_of_lt_left hB1).trans_le hB
  by_cases hεhi : 7 / 18 < ε
  · refine ⟨1, 3, one_pos, by norm_num, ?_⟩
    intro X H hX hlo hhi
    exact (Prep1121KLRough.block_range_empty hX hεhi hlo hhi).elim
  have hε' : ε ≤ 7 / 18 := le_of_not_gt hεhi
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  obtain ⟨X3, hX3, k3⟩ := display52_identity B ε hBpos hε
  obtain ⟨X4, hX4, k4⟩ := logPower_le_block_H B ε hBpos hε
  refine ⟨2 * C1 + 2 * C2, max X1 (max X2 (max X3 X4)), by positivity,
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α hα
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXc : X3 ≤ X :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hX
  have hXd : X4 ≤ X :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hX
  have hX2' : 2 ≤ X := hX1.trans hXa
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hq : 0 ≤ H ^ 2 / Real.log X ^ (A + 2) := by positivity
  obtain ⟨q, a, hcop, hqP, hqQ, hclose⟩ :=
    minor_arc_dirichlet (Real.rpow_pos_of_pos hL B) (k4 X H hXd hH) hα
  have e1 := k1 X H hXa hH hHX α q a hcop hqP hqQ hclose
  have e2 := k2 X H hXb hH hHX α q a hcop hqP hqQ hclose
  unfold roughShortSum
  by_cases hz : windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤
      windowY X ε ^ (1 / 6 + ε / 2)
  · refine (e1 _ hz).trans ?_
    have hr : C1 * H ^ 2 / Real.log X ^ (A + 2) = C1 * (H ^ 2 / Real.log X ^ (A + 2)) := by
      ring
    have hr' : (2 * C1 + 2 * C2) * H ^ 2 / Real.log X ^ (A + 2) =
        (2 * C1 + 2 * C2) * (H ^ 2 / Real.log X ^ (A + 2)) := by ring
    rw [hr, hr']
    exact mul_le_mul_of_nonneg_right (by linarith) hq
  · have hY : 0 < windowY X ε := by
      unfold windowY
      exact Real.rpow_pos_of_pos (by linarith) _
    have hid := k3 X hXc (not_le.mp hz).le
    refine (short_sum_sub_mean_square_le (squareWindow (windowY X ε)) _ _ _
      (fun m : ℕ => (fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
      H _ _ _ _ (by linarith) hid (e1 _ le_rfl) e2).trans ?_
    apply le_of_eq
    ring

/-- The rough block bulk through the finer cuts of Prep1121DKLRoughCut.
CONDITIONAL ON the open LEAF pieces first_rough_block and second_dyadic_block;
first_small_block is proved. -/
theorem rough_block_bulk_cut (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        (∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ (A + 2) :=
  rough_block_bulk_of_sums Prep1121DKLRoughCut.first_sum_block_of_pieces
    Prep1121DKLRoughCut.second_sum_block_of_dyadic A hA

/-- Twin check: the exact type of the sealed leaf Task628.rough_block_bulk. -/
example : type_of% @Task628.rough_block_bulk := rough_block_bulk_cut

/-- Unit P1122-0129, the literal wiring: written Theorem 1 of P0088 page 16 from
majorArcBlockHyp_of_char_inputs and Prep1121KLRough.rough_block_bulk_of_block_leaves.
CONDITIONAL ON A12Corr and A22Corr and on six open leaves: bound27, bound20,
bound24 and bound26 of Prep1121KLMajorArc, and first_sum_block and
second_sum_block of Prep1121KLRoughBulk. -/
theorem thm1_written_of_char_inputs_coarse (hA12 : A12Corr) (hA22 : A22Corr) :
    Task129W.kumchev_liu_thm1_written :=
  DQMajorArcBlock.thm1_written_of_hyps
    (DQMajorArcChar.majorArcBlockHyp_of_char_inputs hA12 hA22)
    rough_block_bulk_of_block_leaves

/-- Units P1122-0129 and P1122-0132, the Palomar headline: P0088 Theorem 1 on the
written range of page 16, exactly Task129W.kumchev_liu_thm1_written, CONDITIONAL
ON the cited A12Corr and A22Corr of page 5, asserted on page 15 by the methods of
Huxley's theorem. It routes through the finest existing cuts, so its open LEAF
pieces are bound27, S2_sub_S2star_major_mean_square, S2star_minor_mean_square,
S1_sub_S1star_on_M0, S2star_M0_L1, first_rough_block and second_dyadic_block,
seven in all by a dependency closure check. Task628.low_H_large_eps is not used. -/
theorem thm1_written_of_char_inputs (hA12 : A12Corr) (hA22 : A22Corr) :
    Task129W.kumchev_liu_thm1_written :=
  DQMajorArcBlock.thm1_written_of_hyps
    (DQMajorArcChar.majorArcBlockHyp_of_char_inputs_cut hA12 hA22)
    rough_block_bulk_cut

/-- P0088 Theorem 1 on its printed range H at most X for epsilon at most 5/18,
from the headline by the proved Task129W.thm1_full_of_written_small_eps.
CONDITIONAL ON A12Corr and A22Corr, with the same open LEAF pieces. -/
theorem thm1_small_eps_of_char_inputs (hA12 : A12Corr) (hA22 : A22Corr)
    (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧
    ∀ δ ε : ℝ, 0 < δ → 0 < ε → ε ≤ 5 / 18 → ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧
      ∀ X H : ℝ, X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K * ‖Task129.main2 X (Task129.windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
          ‖(Task129.primeCount X (Task129.windowY X ε) n : ℂ) -
            Task129.main2 X (Task129.windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
          C * H / Real.log X ^ A :=
  Task129W.thm1_full_of_written_small_eps (thm1_written_of_char_inputs hA12 hA22) A hA

end LeanLab.KumchevLiu2007.DQThm1Char

#print axioms LeanLab.KumchevLiu2007.DQThm1Char.rough_block_bulk_of_sums
#print axioms LeanLab.KumchevLiu2007.DQThm1Char.rough_block_bulk_cut
#print axioms LeanLab.KumchevLiu2007.DQThm1Char.thm1_written_of_char_inputs_coarse
#print axioms LeanLab.KumchevLiu2007.DQThm1Char.thm1_written_of_char_inputs
#print axioms LeanLab.KumchevLiu2007.DQThm1Char.thm1_small_eps_of_char_inputs
