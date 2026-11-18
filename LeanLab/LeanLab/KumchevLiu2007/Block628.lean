/-
P0088 page 8 display 33 from corrected short block inputs.
The old Task556 major transference and character leaves are not used.
The shifted kernel proof and the actual complete rough energy are consumed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.BlockInputs628

namespace LeanLab.KumchevLiu2007.Task628

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Page 8 display 33 on short translated blocks of n. CONDITIONAL ON
major_arc_block and rough_block_energy. The proof uses the clean Fourier
identity, shifted display 29, complete Gallagher energy and the finite
square inequality. It uses no refuted character normalization. -/
theorem weighted_block_mean_square (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X X' H : ℝ,
        X0 ≤ X → X ≤ X' → X' ≤ X + windowY X ε →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∑ n ∈ intervalNumbers X' H, err53 X ε B n ^ 2) ≤
          C * H * windowY X ε / Real.log X ^ A := by
  obtain ⟨B1, hB1, hm⟩ := major_arc_block A hA
  obtain ⟨B2, hB2, he⟩ := rough_block_energy A hA
  refine ⟨max B1 B2, hB1.trans_le (le_max_left _ _), ?_⟩
  intro B hB ε hε
  have hBpos : 0 < B := hB1.trans_le ((le_max_left _ _).trans hB)
  obtain ⟨C1, X1, hC1, hX1, hm⟩ := hm B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, he⟩ := he B ((le_max_right _ _).trans hB) ε hε
  obtain ⟨X3, hX3, hl⟩ := block_length_eventually B ε hε
  refine ⟨4 * C1 + 128 * π ^ 2 * C2, max (max X1 X2) X3, by positivity,
    hX1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro X X' H hX hXX' _hX' hlo hhi
  have hx1 : X1 ≤ X := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
  have hx2 : X2 ≤ X := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
  have hx3 : X3 ≤ X := (le_max_right _ _).trans hX
  have hX3' : 3 ≤ X := hX3.trans hx3
  have hX'0 : 0 ≤ X' := by linarith
  have hH2 : 2 ≤ H := hl X H hx3 hlo
  obtain ⟨_heps, hY1, hYX, hHX⟩ := block_window_parameters hX3' hBpos.le hε hlo hhi
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  have hc : ((intervalNumbers X' H).card : ℝ) ≤ 2 * H := by
    rw [Task556b.intervalNumbers_eq_Ioc hX'0]
    exact Task506aTask271a.interval_card_le hX'0 (by linarith)
  have hmajor : (∑ n ∈ intervalNumbers X' H,
      ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
        2 * C1 * H * windowY X ε / Real.log X ^ A := by
    calc
      _ ≤ ∑ _n ∈ intervalNumbers X' H, C1 * windowY X ε / Real.log X ^ A :=
        Finset.sum_le_sum fun n _ => hm X H hx1 hlo hhi n
      _ = ((intervalNumbers X' H).card : ℝ) *
          (C1 * windowY X ε / Real.log X ^ A) := by simp
      _ ≤ (2 * H) * (C1 * windowY X ε / Real.log X ^ A) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hminor := minor_block_of_complete_energy hX3' hX'0 (by linarith) hY1 hH2 hHX
    hC2.le (he X H hx2 hlo hhi)
  have hs := Task506aTask129b.mean_square_add (intervalNumbers X' H)
    (majorError X (windowY X ε) H (Real.log X ^ B))
    (minorCoefficient X (windowY X ε) H (Real.log X ^ B))
  have herr : ∀ n, err53 X ε B n =
      ‖majorError X (windowY X ε) H (Real.log X ^ B) n +
        minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ := by
    intro n
    unfold err53
    rw [Task556b.error_eq_major_add_minor X ε B H n]
  simp_rw [herr]
  calc _ ≤ _ := hs
    _ ≤ 2 * (2 * C1 * H * windowY X ε / Real.log X ^ A) +
        2 * (64 * π ^ 2 * C2 * H * windowY X ε / Real.log X ^ A) := by
      linarith
    _ = _ := by ring

/-- Page 8 display 33 on the window range, obtained by the proved block
covering argument. CONDITIONAL ON major_arc_block and rough_block_energy.
There is no upper bound H at most X to the one minus epsilon here. -/
theorem weighted_window_mean_square (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ windowY X ε →
        (∑ n ∈ intervalNumbers X H, err53 X ε B n ^ 2) ≤
          C * H * windowY X ε / Real.log X ^ A := by
  exact Eq33Window1117.eq33_window_range_of_blocks A hA (weighted_block_mean_square A hA)

/-- Pages 4 and 6, a nonvacuity check for the repaired block range.
For every fixed B and epsilon between zero and seven eighteenths there are
arbitrarily large X with an admissible block of length at least two. -/
theorem block_range_nonempty (B ε R : ℝ) (hε : 0 < ε) (hεhi : ε ≤ 7 / 18) :
    ∃ X H : ℝ, 3 ≤ X ∧ R ≤ X ∧ 2 ≤ H ∧
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H ∧
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) := by
  obtain ⟨X0, hX0, hl⟩ := block_length_eventually B ε hε
  let X := max X0 R
  let H := windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ)
  have hX3 : 3 ≤ X := hX0.trans (le_max_left _ _)
  have hX1 : 1 ≤ X := by linarith
  have hP : 0 ≤ (Real.log X ^ B) ^ (-4 : ℤ) := by positivity
  have hlo : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H := by
    apply mul_le_mul_of_nonneg_right _ hP
    unfold windowY
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  exact ⟨X, H, hX3, le_max_right _ _, hl X H (le_max_left _ _) hlo, hlo, le_rfl⟩

end LeanLab.KumchevLiu2007.Task628

#print axioms LeanLab.KumchevLiu2007.Task628.weighted_block_mean_square
#print axioms LeanLab.KumchevLiu2007.Task628.weighted_window_mean_square
#print axioms LeanLab.KumchevLiu2007.Task628.block_range_nonempty
