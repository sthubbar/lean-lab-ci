/-
CITED WALL decision for Task628.rough_block_bulk, BlockInputs628.lean.
P0088, Kumchev and Liu, arXiv 0801.0130.

DECISION. NAMED HYPOTHESIS. The leaf is hypothesis A2.3 of page 7 for the
rough weight lambda_0 = Phi(m, z0), z0 = Y^(1/4) P^(-2) of page 8 display 34,
as verified on page 15 after display 52 by Lemma 3.4 of page 11 applied to the
two sums of display 52. That verification is a published lemma of the paper,
whose proof uses Lemmas 3.1 to 3.3 and the bilinear Weyl machinery of pages
9 to 12; it is not short. The lab already splits it in Eq33RouteD and the two
SPLIT_lemma34 files, which stay open.

The named hypothesis RoughA23Hyp below is A2.3 for lambda_0 in the paper's
own parameters: Y = X^(7/12 + eps/2), the page 15 condition theta_2 at least
2/3 + eta written as Y^(2/3 + eta) at most H, and P = (log X)^B. The leaf
differs from the paper only in its H range, which loses four powers of P at
the lower end; the proved margin lemmas below absorb that loss, choosing
eta = eps / 4.

rough_block_bulk_of_hyp proves the exact statement of Task628.rough_block_bulk
from RoughA23Hyp with no admitted step. rough_block_energy_of_hyp then proves the
exact statement of Task628.rough_block_energy from it.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.BlockInputs628

namespace LeanLab.KumchevLiu2007.DQRoughBlockBulk

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Task628
open scoped BigOperators Topology

/-- NAMED HYPOTHESIS, cited published lemma. P0088 page 7 hypothesis A2.3 for
lambda_2 = lambda_0 = Phi(m, z0) of page 8 display 34, as established on
page 15 after display 52 by Lemma 3.4 of page 11 with x = Y, y = H and
z = z1 = Y^(1/6 + eta/2), where eta is the page 15 margin in theta_2 at least
2/3 + eta. Here Y = X^(7/12 + eps/2), page 16, P = (log X)^B and the minor
arcs are the complement of the major arcs of page 4 displays 14 and 15.
The short sum keeps m in I2 of page 2 display 5, as Gallagher's lemma on
page 8 uses it; the edge terms differ from the unrestricted page 7 sum by
O(H^3 / Y), which the upper bound H at most Y L^(-A) absorbs. The window
exponent is kept at most 7/18, where Y is below X. -/
def RoughA23Hyp : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
    ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε / Real.log X ^ A →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        (∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A

/-- P0088 page 15 and page 16: the leaf's lower block length
X^(7/18 + eps) P^(-4) is at least Y^(2/3 + eps/4) for large X. The exponent
gap is at least eps / 4, which absorbs P^4. -/
theorem lower_margin (B ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 7 / 18) :
    ∃ X1 : ℝ, 3 ≤ X1 ∧ ∀ X : ℝ, X1 ≤ X →
      windowY X ε ^ (2 / 3 + ε / 4) ≤
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) := by
  have ht := (isLittleO_log_rpow_rpow_atTop B (by positivity : (0 : ℝ) < ε / 16)).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨X0, h0⟩ := Filter.eventually_atTop.mp ht
  refine ⟨max 3 X0, le_max_left _ _, fun X hX => ?_⟩
  have hX3 : 3 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have h := h0 X ((le_max_right _ _).trans hX)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hP,
    abs_of_pos (Real.rpow_pos_of_pos hX0 _)] at h
  have h4 : (Real.log X ^ B) ^ 4 ≤ X ^ (ε / 4) := by
    calc (Real.log X ^ B) ^ 4 ≤ (X ^ (ε / 16)) ^ 4 := pow_le_pow_left₀ hP.le h 4
      _ = X ^ (ε / 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
        congr 1
        push_cast
        ring
  unfold windowY
  rw [← Real.rpow_mul hX0.le, zpow_neg, zpow_ofNat, ← div_eq_mul_inv,
    le_div_iff₀ (pow_pos hP 4)]
  have hexp : (7 / 12 + ε / 2) * (2 / 3 + ε / 4) + ε / 4 ≤ 7 / 18 + ε := by
    nlinarith
  calc X ^ ((7 / 12 + ε / 2) * (2 / 3 + ε / 4)) * (Real.log X ^ B) ^ 4
      ≤ X ^ ((7 / 12 + ε / 2) * (2 / 3 + ε / 4)) * X ^ (ε / 4) := by gcongr
    _ = X ^ ((7 / 12 + ε / 2) * (2 / 3 + ε / 4) + ε / 4) := by
        rw [← Real.rpow_add hX0]
    _ ≤ X ^ (7 / 18 + ε) := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp

/-- The leaf's upper block length Y P^(-4) is at most Y L^(-(A + 2)) once
4 B is at least A + 2. -/
theorem upper_margin {X B A Y : ℝ} (hX : 3 ≤ X) (hY : 0 ≤ Y)
    (hAB : A + 2 ≤ 4 * B) :
    Y * (Real.log X ^ B) ^ (-4 : ℤ) ≤ Y / Real.log X ^ (A + 2) := by
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact Real.exp_one_lt_three.le.trans hX
  have hL : 0 < Real.log X := by linarith
  have he : (Real.log X ^ B) ^ 4 = Real.log X ^ (4 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    push_cast
    ring
  rw [zpow_neg, zpow_ofNat, he, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hY (Real.rpow_pos_of_pos hL _)
    (Real.rpow_le_rpow_of_exponent_le hL1 hAB)

/-- P0088 page 7 A2.3 and page 15 display 52 on short blocks: the exact
statement of Task628.rough_block_bulk. Above eps = 7/18 the block range is
empty. CONDITIONAL ON RoughA23Hyp; no admitted step. -/
theorem rough_block_bulk_of_hyp (h : RoughA23Hyp) (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        (∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ (A + 2) := by
  obtain ⟨B0, hB0, hb⟩ := h (A + 2) (by linarith)
  refine ⟨max B0 ((A + 2) / 4), hB0.trans_le (le_max_left _ _), ?_⟩
  intro B hB ε hε
  have hAB : A + 2 ≤ 4 * B := by linarith [le_max_right B0 ((A + 2) / 4)]
  by_cases hε7 : ε ≤ 7 / 18
  · obtain ⟨C, X0, hC, hX0, hk⟩ :=
      hb B ((le_max_left _ _).trans hB) ε hε hε7 (ε / 4) (by positivity)
    obtain ⟨X1, hX1, hm⟩ := lower_margin B ε hε hε7
    refine ⟨C, max X0 X1, hC, hX0.trans (le_max_left _ _), ?_⟩
    intro X H hX hlo hhi α hα
    have hx0 : X0 ≤ X := (le_max_left _ _).trans hX
    have hx1 : X1 ≤ X := (le_max_right _ _).trans hX
    have hX3 : 3 ≤ X := hX1.trans hx1
    have hY : 0 ≤ windowY X ε := (Real.rpow_pos_of_pos (by linarith) _).le
    exact hk X H hx0 ((hm X hx1).trans hlo) (hhi.trans (upper_margin hX3 hY hAB)) α hα
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

/-- P0088 pages 7 and 8: the exact statement of Task628.rough_block_energy,
the bulk from RoughA23Hyp plus the proved initial interval bound
Task628.block_initial_energy. CONDITIONAL ON RoughA23Hyp; no admitted step. -/
theorem rough_block_energy_of_hyp (h : RoughA23Hyp) (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        ((∫ t in (windowY X ε / 4 - H)..(windowY X ε / 4),
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) +
          ∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ (A + 2) := by
  obtain ⟨B0, hB0, hb⟩ := rough_block_bulk_of_hyp h A hA
  refine ⟨max B0 (A + 2), hB0.trans_le (le_max_left _ _), ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hb⟩ := hb B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨X1, hX1, hr⟩ := block_root_eventually B ε hε
  refine ⟨4 + C, max X0 X1, by positivity, hX0.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α hα
  have hx0 : X0 ≤ X := (le_max_left _ _).trans hX
  have hx1 : X1 ≤ X := (le_max_right _ _).trans hX
  have hX3 : 3 ≤ X := hX1.trans hx1
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  have hB' : A + 2 ≤ 4 * B := by linarith [le_trans (le_max_right B0 (A + 2)) hB]
  have hi := block_initial_energy (α := α) hX3 hY (hr X H hx1 hlo) hB' hhi
  have hm := hb X H hx0 hlo hhi α hα
  calc _ ≤ 4 * H ^ 2 / Real.log X ^ (A + 2) + C * H ^ 2 / Real.log X ^ (A + 2) :=
        add_le_add hi hm
    _ = _ := by ring

/-- Twin check: the conditional theorem inhabits exactly the type of the
sealed leaf Task628.rough_block_bulk. -/
example (h : RoughA23Hyp) : type_of% @Task628.rough_block_bulk :=
  rough_block_bulk_of_hyp h

/-- Twin check: the conditional energy theorem inhabits exactly the type of
Task628.rough_block_energy. -/
example (h : RoughA23Hyp) : type_of% @Task628.rough_block_energy :=
  rough_block_energy_of_hyp h

end LeanLab.KumchevLiu2007.DQRoughBlockBulk

#print axioms LeanLab.KumchevLiu2007.DQRoughBlockBulk.lower_margin
#print axioms LeanLab.KumchevLiu2007.DQRoughBlockBulk.upper_margin
#print axioms LeanLab.KumchevLiu2007.DQRoughBlockBulk.rough_block_bulk_of_hyp
#print axioms LeanLab.KumchevLiu2007.DQRoughBlockBulk.rough_block_energy_of_hyp
