/-
Wiring unit P1122-0128, burst-20261122, session S33. P0088, Kumchev and Liu,
arXiv 0801.0130, page 7 display 28 squared, the named MajorArcBlockHyp of
DQMajorArcBlockDecisions, from the cited character inputs A12Corr and A22Corr.

major_arc_block_of_bounds is the page 7 assembly of display 28 from displays
20, 24, 26 and 27 with those four error bounds as hypotheses; the proof is the
proof of Prep1121KLMajor.major_arc_block_of_char_inputs with the four leaves
replaced by arguments, so it holds no sorry and no leaf. It lets the finer cuts
of Prep1121DKLMajorCut, which cannot be imported by Prep1121KLMajorArc, feed
the named hypothesis directly.

majorArcBlockHyp_of_char_inputs is the literal wiring through
Prep1121KLMajor.major_arc_block_of_char_inputs. majorArcBlockHyp_of_char_inputs_cut
is the same conclusion through the finer pieces bound20_of_pieces,
bound24_of_pieces and bound26_of_pieces; bound27 is still the coarse leaf of
Prep1121KLMajorArc, since no cut of it exists yet. Both are CONDITIONAL ON
A12Corr and A22Corr and carry the open LEAF pieces beneath them as sorryAx.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121DKLMajorCut
import LeanLab.KumchevLiu2007.DQMajorArcBlockDecisions

namespace LeanLab.KumchevLiu2007.DQMajorArcChar

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 7 display 28 squared, the named DQMajorArcBlock.MajorArcBlockHyp,
from page 7 display 27, page 6 displays 20, 24 and 26 as the four error bounds
h27, h20, h24, h26, the proved first line of display 28, major_decomp, and the
proved Fourier split of displays 13 and 15. No sorry of its own. -/
theorem major_arc_block_of_bounds
    (h27 : BlockErrorBound
      (fun X Y H P n => termA X Y H P n - series2 n P * (singInt X Y P n : ℂ)))
    (h20 : BlockErrorBound termB) (h24 : BlockErrorBound termC)
    (h26 : BlockErrorBound termD) : DQMajorArcBlock.MajorArcBlockHyp := by
  intro A hA
  refine ⟨2 * A + 1, by linarith, ?_⟩
  intro B hB ε hε
  have hBpos : 0 < B := by linarith
  by_cases hεhi : 7 / 18 < ε
  · refine ⟨1, 3, one_pos, by norm_num, ?_⟩
    intro X H hX hlo hhi n
    exact (block_range_empty hX hεhi hlo hhi).elim
  have hε' : ε ≤ 7 / 18 := le_of_not_gt hεhi
  obtain ⟨X0, hdec⟩ := major_decomp B hBpos ε hε hε'
  obtain ⟨C1, X1, hC1, h27⟩ := h27 B hBpos ε hε hε'
  obtain ⟨C2, X2, hC2, h20⟩ := h20 B hBpos ε hε hε'
  obtain ⟨C3, X3, hC3, h24⟩ := h24 B hBpos ε hε hε'
  obtain ⟨C4, X4, hC4, h26⟩ := h26 B hBpos ε hε hε'
  set K := C1 + C2 + C3 + C4 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨K ^ 2, max (max (max X0 X1) (max X2 X3)) (max X4 3), by positivity,
    le_trans (by norm_num) (le_max_right _ _ |>.trans (le_max_right _ _)), ?_⟩
  intro X H hX hlo hhi n
  have hX0 : X0 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_left _ _ |>.trans
    (le_max_left _ _))) hX
  have hX1 : X1 ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_left _ _ |>.trans
    (le_max_left _ _))) hX
  have hX2 : X2 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_right _ _ |>.trans
    (le_max_left _ _))) hX
  have hX3 : X3 ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_right _ _ |>.trans
    (le_max_left _ _))) hX
  have hX4 : X4 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_right _ _)) hX
  have hX5 : (3 : ℝ) ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_right _ _)) hX
  set Y := windowY X ε with hY
  set L := Real.log X with hLdef
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX5
  have hLpos : 0 < L := by linarith
  have hYnn : 0 ≤ Y := Real.rpow_nonneg hXpos.le _
  set E := ‖majorError X Y H (L ^ B) n‖ with hE
  set R := (L ^ B) ^ (-(1 / 4 : ℝ)) with hR
  have hRnn : 0 ≤ R := Real.rpow_nonneg (Real.rpow_nonneg hLpos.le _) _
  have hsplit : majorError X Y H (L ^ B) n =
      (termA X Y H (L ^ B) n - series2 n (L ^ B) * (singInt X Y (L ^ B) n : ℂ)) +
        termB X Y H (L ^ B) n + termC X Y H (L ^ B) n + termD X Y H (L ^ B) n := by
    rw [majorError, roughCount_eq_major_add_minor X Y H (L ^ B) n,
      hdec X H hX0 hlo hhi n]
    ring
  have hbound : E ≤ K * Real.sqrt Y * R := by
    rw [hE, hsplit]
    have a1 := h27 X H hX1 hlo hhi n
    have a2 := h20 X H hX2 hlo hhi n
    have a3 := h24 X H hX3 hlo hhi n
    have a4 := h26 X H hX4 hlo hhi n
    calc _ ≤ ‖termA X Y H (L ^ B) n - series2 n (L ^ B) * (singInt X Y (L ^ B) n : ℂ)‖ +
          ‖termB X Y H (L ^ B) n‖ + ‖termC X Y H (L ^ B) n‖ + ‖termD X Y H (L ^ B) n‖ :=
            norm_add₄_le
      _ ≤ C1 * Real.sqrt Y * R + C2 * Real.sqrt Y * R + C3 * Real.sqrt Y * R +
          C4 * Real.sqrt Y * R := by gcongr
      _ = K * Real.sqrt Y * R := by rw [hK]; ring
  have hRsq : R ^ 2 ≤ L ^ (-A) := by
    have h1 : R = L ^ (B * (-(1 / 4 : ℝ))) := by rw [hR, ← Real.rpow_mul hLpos.le]
    have h2 : R ^ 2 = L ^ (-(B / 2)) := by
      rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
      congr 1
      push_cast
      ring
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hEnn : 0 ≤ E := norm_nonneg _
  calc E ^ 2 ≤ (K * Real.sqrt Y * R) ^ 2 := pow_le_pow_left₀ hEnn hbound 2
    _ = K ^ 2 * Y * R ^ 2 := by rw [mul_pow, mul_pow, Real.sq_sqrt hYnn]
    _ ≤ K ^ 2 * Y * L ^ (-A) := by gcongr
    _ = K ^ 2 * Y / L ^ A := by rw [Real.rpow_neg hLpos.le, div_eq_mul_inv]

/-- Unit P1122-0128: MajorArcBlockHyp from A12Corr and A22Corr through
Prep1121KLMajor.major_arc_block_of_char_inputs. CONDITIONAL ON A12Corr and
A22Corr, with the open leaves bound27, bound20, bound24 and bound26 of
Prep1121KLMajorArc beneath it. -/
theorem majorArcBlockHyp_of_char_inputs (hA12 : A12Corr) (hA22 : A22Corr) :
    DQMajorArcBlock.MajorArcBlockHyp :=
  fun A hA => major_arc_block_of_char_inputs hA12 hA22 A hA

/-- The same conclusion through the finer cuts of Prep1121DKLMajorCut for
displays 20, 24 and 26, and the coarse leaf bound27 for display 27.
CONDITIONAL ON A12Corr and A22Corr, with the open LEAF pieces
S2_sub_S2star_major_mean_square, S2star_minor_mean_square,
S1_sub_S1star_on_M0, S2star_M0_L1 and bound27 beneath it. -/
theorem majorArcBlockHyp_of_char_inputs_cut (hA12 : A12Corr) (hA22 : A22Corr) :
    DQMajorArcBlock.MajorArcBlockHyp :=
  major_arc_block_of_bounds (bound27 T1_bound T2_bound)
    (Prep1121DKLMajorCut.bound20_of_pieces hA22)
    (Prep1121DKLMajorCut.bound24_of_pieces T2_bound)
    (Prep1121DKLMajorCut.bound26_of_pieces hA12 T2_bound)

/-- Twin check: the wiring has the exact type of the sealed leaf Task628.major_arc_block. -/
example (hA12 : A12Corr) (hA22 : A22Corr) : type_of% @Task628.major_arc_block :=
  DQMajorArcBlock.major_arc_block_of_hyp (majorArcBlockHyp_of_char_inputs_cut hA12 hA22)

end LeanLab.KumchevLiu2007.DQMajorArcChar

#print axioms LeanLab.KumchevLiu2007.DQMajorArcChar.major_arc_block_of_bounds
#print axioms LeanLab.KumchevLiu2007.DQMajorArcChar.majorArcBlockHyp_of_char_inputs
#print axioms LeanLab.KumchevLiu2007.DQMajorArcChar.majorArcBlockHyp_of_char_inputs_cut
