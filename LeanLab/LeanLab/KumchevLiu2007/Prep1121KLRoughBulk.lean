/-
PREP 2026-11-21, KL-cited splitter. SPLIT of Task628.rough_block_bulk, BlockInputs628.lean.
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 15 display 52 and the
paragraph after it, with Lemma 3.4 of page 11.

DECISION. The step is IN PLACE: page 15 derives hypothesis A2.3 for lambda0 from
display 52 and two applications of the paper's own Lemma 3.4, whose proof is
printed on pages 11 and 12. The citation wall sits one level lower: Lemma 3.4
uses Lemmas 3.1 and 3.2, restatements of Lemmas 3.1 and 3.2 of reference 14
with proofs omitted, and Lemma 3.3, Kumchev reference 12 Lemma 2.7.

Eq33RouteD already proves this route, but only in the written range
X^(7/18 + eps) at most H at most X^(1 - eps). The sealed leaf needs the block
range X^(7/18 + eps) P^(-4) at most H at most Y P^(-4), whose lower end is
four logarithmic powers lower. This file restates the two Lemma 3.4
applications in the block range as two LEAF lemmas, proves the log power
margin logPower_le_block_H, and proves the exact statement
of Task628.rough_block_bulk from them with the proved Eq33RouteD tools:
display52_identity, minor_arc_dirichlet and short_sum_sub_mean_square_le.
In the block range z1 Y^(1/2) = Y^(2/3 + eps/2) is below H by a power of X,
since (7/12 + eps/2)(2/3 + eps/2) is less than 7/18 + eps, so the cutoff
condition of Lemma 3.4 still holds.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.BlockInputs628
import LeanLab.KumchevLiu2007.Eq33RouteD

namespace LeanLab.KumchevLiu2007.Prep1121KLRough

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11 Lemma 3.4 as applied on page 15 after display 52 to the first
sum of display 52, x = Y, y = H, (m, k) = (1, m), cutoff z at most z1 = Y^(1/6 + eps/2),
alpha satisfying display 41 with y = H. Same as Eq33RouteD.lemma34_first_sum, in the
block range of Task628.rough_block_bulk. -/
theorem first_sum_block (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 11 Lemma 3.4 as applied on page 15 after display 52 to the second
sum of display 52, x = Y, y = H, (m, k) = (p, m/p), z = z1, primes p from z1 to below
z0 = Y^(1/4) P^(-2) of display 34. Same as Eq33RouteD.lemma34_second_sum, in the block
range; the dyadic reduction of Eq33RouteD.lemma34_second_sum carries over. -/
theorem second_sum_block (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- PROVED. P0088 page 4 display 14 in the block range: Q = H/P is at least one, as
needed for Dirichlet's theorem. The lower block end X^(7/18 + eps) P^(-4) exceeds
P = (log X)^B for large X; an elementary log power comparison. -/
theorem logPower_le_block_H (B ε : ℝ) (_hB : 0 < B) (hε : 0 < ε) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H → Real.log X ^ B ≤ H := by
  have ht := (isLittleO_log_rpow_rpow_atTop (5 * B)
    (by positivity : (0 : ℝ) < 7 / 18 + ε)).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨X0, h0⟩ := Filter.eventually_atTop.mp ht
  refine ⟨max 2 X0, le_max_left _ _, fun X H hX hH => ?_⟩
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have h := h0 X ((le_max_right _ _).trans hX)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL _),
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)] at h
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have h5 : Real.log X ^ (5 * B) = (Real.log X ^ B) ^ (5 : ℕ) := by
    rw [show (5 : ℝ) * B = B * ((5 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul hL.le, Real.rpow_natCast]
  rw [h5] at h
  have hz : 0 ≤ (Real.log X ^ B) ^ (-4 : ℤ) := (zpow_pos hP _).le
  calc Real.log X ^ B = (Real.log X ^ B) ^ (5 : ℕ) * (Real.log X ^ B) ^ (-4 : ℤ) := by
        rw [zpow_neg, zpow_ofNat]
        field_simp
    _ ≤ X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) :=
        mul_le_mul_of_nonneg_right h hz
    _ ≤ H := hH

/-- P0088 page 16: for eps above 7/18 the block range is empty. -/
theorem block_range_empty {X H B ε : ℝ} (hX : 3 ≤ X) (hε : 7 / 18 < ε)
    (hlo : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H)
    (hhi : H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ)) : False := by
  have hX1 : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  have hP : 0 < (Real.log X ^ B) ^ (-4 : ℤ) := zpow_pos (Real.rpow_pos_of_pos hL _) _
  have h := (mul_le_mul_iff_left₀ hP).mp (hlo.trans hhi)
  rw [windowY] at h
  have h2 := (Real.rpow_le_rpow_left_iff hX1).mp h
  linarith

/-- P0088 page 15 after display 52: the exact statement of Task628.rough_block_bulk,
from the two leaves above, logPower_le_block_H and the proved display52_identity, minor_arc_dirichlet
and short_sum_sub_mean_square_le of Eq33RouteD. No sorry of its own. -/
theorem rough_block_bulk_of_block_leaves (A : ℝ) (hA : 0 < A) :
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
  obtain ⟨B1, hB1, h1⟩ := first_sum_block (A + 2) hA2
  obtain ⟨B2, hB2, h2⟩ := second_sum_block (A + 2) hA2
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε => ?_⟩
  have hBpos : 0 < B := (lt_max_of_lt_left hB1).trans_le hB
  by_cases hεhi : 7 / 18 < ε
  · refine ⟨1, 3, one_pos, by norm_num, ?_⟩
    intro X H hX hlo hhi
    exact (block_range_empty hX hεhi hlo hhi).elim
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

/-- The theorem above has the exact type of the sealed leaf Task628.rough_block_bulk. -/
example : type_of% @Task628.rough_block_bulk := rough_block_bulk_of_block_leaves

end LeanLab.KumchevLiu2007.Prep1121KLRough

#print axioms LeanLab.KumchevLiu2007.Prep1121KLRough.rough_block_bulk_of_block_leaves
#print axioms LeanLab.KumchevLiu2007.Prep1121KLRough.block_range_empty
#print axioms LeanLab.KumchevLiu2007.Prep1121KLRough.logPower_le_block_H
