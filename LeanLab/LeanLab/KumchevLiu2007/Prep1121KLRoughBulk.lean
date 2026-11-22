/-
Prep unit for Task628.rough_block_bulk on the repaired short blocks, FREE-nv-glm
task2227. P0088, Kumchev and Liu, arXiv 0801.0130.

block_range_cutoff_margin confirms the Lemma 3.4 cutoff margin on the block
range: with z1 = Y^(1/6 + eps/2) of page 15 after display 52 and Y =
X^(7/12 + eps/2) of page 16, the product z1 * sqrt Y equals Y^(2/3 + eps/2),
and on the block lower end X^(7/18 + eps) P^(-4) this stays below H because
the exponent gap at least 5 eps / 18 absorbs the four powers of P = L^B.

rough_block_bulk_of_block_leaves proves the exact statement of the sealed
Task628.rough_block_bulk from the named block leaf hypothesis RoughA23Hyp,
page 7 hypothesis A2.3 for lambda_0 = Phi(m, z0) with z0 = Y^(1/4) P^(-2),
as established on page 15 by Lemma 3.4 of page 11 applied to the two sums
of display 52. CONDITIONAL ON RoughA23Hyp; no admitted step.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.DQRoughBlockBulkDecisions

namespace LeanLab.KumchevLiu2007.Prep1121KLRoughBulk

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Task628
open scoped BigOperators Topology

/-- P0088 page 15 after display 52 with page 11 Lemma 3.4, on the repaired
block range: the cutoff product z1 * sqrt Y with z1 = Y^(1/6 + eps/2) is at
most the block lower end X^(7/18 + eps) P^(-4), hence at most H. The power
margin 5 eps / 18 absorbs P^4. Proved parameter lemma, burst unit P1122-0148
repair audit of the block range Lemma 3.4 cutoff margin. -/
theorem block_range_cutoff_margin (B ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 7 / 18) :
    ∃ X1 : ℝ, 3 ≤ X1 ∧ ∀ X H : ℝ, X1 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      windowY X ε ^ (1 / 6 + ε / 2) * Real.sqrt (windowY X ε) ≤ H := by
  have hd : (0 : ℝ) < 5 * ε / 18 := by positivity
  have ht := (isLittleO_log_rpow_rpow_atTop (4 * B) hd).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨X0, h0⟩ := Filter.eventually_atTop.mp ht
  refine ⟨max 3 X0, le_max_left _ _, fun X H hX hH => ?_⟩
  have hX3 : 3 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hP4 : 0 < Real.log X ^ (4 * B) := Real.rpow_pos_of_pos hL (4 * B)
  have h := h0 X ((le_max_right _ _).trans hX)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hP4,
    abs_of_pos (Real.rpow_pos_of_pos hX0 _)] at h
  have he4 : (Real.log X ^ B) ^ 4 = Real.log X ^ (4 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    push_cast
    ring
  have h4 : (Real.log X ^ B) ^ 4 ≤ X ^ (5 * ε / 18) := by
    rw [he4]
    exact h
  have hY : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos hX0 _
  have hz : windowY X ε ^ (1 / 6 + ε / 2) * Real.sqrt (windowY X ε) =
      windowY X ε ^ (2 / 3 + ε / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hY]
    congr 1
    ring
  have hmain : windowY X ε ^ (2 / 3 + ε / 2) ≤
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) := by
    rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hP 4)]
    unfold windowY
    rw [← Real.rpow_mul hX0.le]
    calc X ^ ((7 / 12 + ε / 2) * (2 / 3 + ε / 2)) * (Real.log X ^ B) ^ 4
        ≤ X ^ ((7 / 12 + ε / 2) * (2 / 3 + ε / 2)) * X ^ (5 * ε / 18) := by gcongr
      _ = X ^ ((7 / 12 + ε / 2) * (2 / 3 + ε / 2) + 5 * ε / 18) := by
          rw [← Real.rpow_add hX0]
      _ ≤ X ^ (7 / 18 + ε) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
  rw [hz]
  exact hmain.trans hH

/-- P0088 page 7 hypothesis A2.3 and page 15 display 52 on short blocks: the
exact statement of the sealed Task628.rough_block_bulk, proved from the named
block leaf hypothesis RoughA23Hyp with the proved block range margins of
DQRoughBlockBulkDecisions. CONDITIONAL ON RoughA23Hyp; no admitted step. -/
theorem rough_block_bulk_of_block_leaves (h : DQRoughBlockBulk.RoughA23Hyp)
    (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        (∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ (A + 2) :=
  DQRoughBlockBulk.rough_block_bulk_of_hyp h A hA

/-- Twin check: the conditional theorem inhabits exactly the type of the
sealed leaf Task628.rough_block_bulk. -/
example (h : DQRoughBlockBulk.RoughA23Hyp) :
    type_of% @Task628.rough_block_bulk :=
  rough_block_bulk_of_block_leaves h

end LeanLab.KumchevLiu2007.Prep1121KLRoughBulk

#print axioms LeanLab.KumchevLiu2007.Prep1121KLRoughBulk.block_range_cutoff_margin
#print axioms LeanLab.KumchevLiu2007.Prep1121KLRoughBulk.rough_block_bulk_of_block_leaves
