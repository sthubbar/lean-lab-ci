import Mathlib
import LeanLab.Pintz2021.Audit168
import LeanLab.Pintz2021.Statements
import LeanLab.Pintz2021.Reduction3
import LeanLab.Pintz2021.Lemma1U1369
import LeanLab.Pintz2021.WeightedKernelsTask08
import LeanLab.Pintz2021.DifferenceTask53
import LeanLab.Pintz2021.State1581
import LeanLab.Pintz2021.Applications
import LeanLab.Pintz2021.DecompJ281
import LeanLab.Pintz2021.DecompJ665

open Filter Topology Real Complex
open scoped Topology
open LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.Pintz2021.State1581 LeanLab.Pintz2021.DifferenceTask53
open LeanLab.Pintz2021.DecompJ281
open LeanLab.Pintz2021.DecompJ665

namespace LeanLab.Pintz2021.DecompJ834

/-- REFUTED, `DecompJ665.P_leaf_false`, no `0 < ε`. Repaired in `DecompJ579.leaf_P_exists`. Do not prove this.
LEAF arXiv:1804.05561v1 display 8.28: the major arc parameter P exists -/
theorem leaf_P_exists_3 {ε H0 X0 H X P0 : ℝ} (hHyp : Thm1Hyp ε H0 X0 H X P0) :
  ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧ (excSet H (Real.sqrt X) P X).Finite := by sorry

/-- LEAF arXiv:1804.05561v1 display 9.16: the singular series converges -/
theorem leaf_singular_series_converges_3 (H X P : ℝ) :
  ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m)) := by sorry

/-- REFUTED given `leaf_singular_series_converges_3`, `Audit1614.old_leaf_main_term_bound_exists_C_false_of_converges`: `C` is universal, take `C = -1`. Use `DecompJ579.leaf_main_term_bound`. Do not prove this.
LEAF arXiv:1804.05561v1 display 10.25: the main term error is bounded by a constant C depending only on ε -/
theorem leaf_main_term_bound_exists_C_3 (ε ε0 c H0 C X0 : ℝ) :
  ∀ H X P0 P : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    Thm1Hyp ε H0 X0 H X P0 →
    P0 * X ^ (-ε) ≤ P → P ≤ P0 →
    (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) →
    ∀ m : ℕ, (m : ℝ) ≤ X → 0 < m →
      ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
        C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by sorry

/-- LEAF arXiv:1804.05561v1 display 8.28: the epsilon threshold and core constants exist -/
theorem leaf_constants_exist_3 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c := by
  exact ⟨1, one_pos, fun _ _ _ => ⟨1, 0, 0, 0, one_pos⟩⟩

/-- Assembly of Theorem 1 display 2.21 (untruncated form). -/
theorem assembly_321_3 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c ∧ ∀ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, (m : ℝ) ≤ X → 0 < m →
            ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by
  obtain ⟨ε0, hε0, h1⟩ := leaf_constants_exist_3
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hε0'
  obtain ⟨c, H0, C, X0, hc⟩ := h1 ε hε hε0'
  refine ⟨c, H0, C, X0, hc, ?_⟩
  intro H X P0 hHyp
  obtain ⟨P, hP1, hP2, hFin⟩ := leaf_P_exists_3 hHyp
  refine ⟨P, hP1, hP2, hFin, ?_⟩
  obtain ⟨Sg', hSg1⟩ := leaf_singular_series_converges_3 H X P
  refine ⟨Sg', hSg1, ?_⟩
  exact leaf_main_term_bound_exists_C_3 ε ε0 c H0 C X0 H X P0 P Sg' hHyp hP1 hP2 hSg1

/-- LEAF arXiv:1804.05561v1 display 10.27: the truncated tail error is bounded -/
theorem leaf_truncation_error_3 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ H0 C' X0 : ℝ, 0 < C' ∧ ∀ H X P0 P U : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ, ∀ m : ℕ,
      Thm1Hyp ε H0 X0 H X P0 → P ≤ P0 →
      (excSet H (Real.sqrt X) P X).Finite →
      (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ n : ℕ, 0 < n →
        Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg' z w n))) →
      X / 4 ≤ m → (m : ℝ) ≤ X / 2 → 2 ≤ U →
      ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
        mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
      C' * (Sing m * X * Real.log U / Real.sqrt U) := by sorry

/-- LEAF Assembly of Theorem 1 display 2.22 (truncated form). -/
theorem assembly_322_3 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C C' X0 : ℝ, 0 < c ∧ ∀ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, X / 4 ≤ m ∧ (m : ℝ) ≤ X / 2 →
            ‖R1majPrime ε X P m - mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P (Real.sqrt X) m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) + C' * (Sing m * X * Real.log (Real.sqrt X) / (Real.sqrt (Real.sqrt X))) := by
  obtain ⟨ε1, hε1, h1⟩ := leaf_constants_exist_3
  obtain ⟨ε2, hε2, h2⟩ := leaf_truncation_error_3
  refine ⟨min ε1 ε2, lt_min hε1 hε2, ?_⟩
  intro ε hε hεlt
  obtain ⟨c, H0a, Ca, X0a, hc⟩ := h1 ε hε (lt_of_lt_of_le hεlt (min_le_left ε1 ε2))
  obtain ⟨H0b, C', X0b, hC'⟩ := h2 ε hε (lt_of_lt_of_le hεlt (min_le_right ε1 ε2))
  refine ⟨c, max H0a H0b, Ca, C', max (max X0a X0b) 4, hc, ?_⟩
  intro H X P0 hHyp
  obtain ⟨hH0, hHlog, hX0, hP01, hP0X⟩ := hHyp
  have hXa : X0a ≤ X := le_trans (le_trans (le_max_left X0a X0b) (le_max_left _ 4)) hX0
  have hXb : X0b ≤ X := le_trans (le_trans (le_max_right X0a X0b) (le_max_left _ 4)) hX0
  have hX4 : (4 : ℝ) ≤ X := le_trans (le_max_right _ 4) hX0
  have hHA : Thm1Hyp ε H0a X0a H X P0 :=
    ⟨le_trans (le_max_left H0a H0b) hH0, hHlog, hXa, hP01, hP0X⟩
  have hHB : Thm1Hyp ε H0b X0b H X P0 :=
    ⟨le_trans (le_max_right H0a H0b) hH0, hHlog, hXb, hP01, hP0X⟩
  obtain ⟨P, hP1, hP2, hFin⟩ := leaf_P_exists_3 hHA
  obtain ⟨Sg', hSg⟩ := leaf_singular_series_converges_3 H X P
  refine ⟨P, hP1, hP2, hFin, Sg', hSg, ?_⟩
  intro m hm
  have hmX : (m : ℝ) ≤ X := by linarith [hm.2]
  have hmpos : 0 < m := by
    have h1m : (1 : ℝ) ≤ (m : ℝ) := by linarith [hm.1]
    have : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one h1m
    exact_mod_cast this
  have hU2 : (2 : ℝ) ≤ Real.sqrt X := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hX4
  have hb1 := leaf_main_term_bound_exists_C_3 ε (min ε1 ε2) c H0a Ca X0a H X P0 P Sg' hHA hP1
    hP2 hSg m hmX hmpos
  have hb2 := hC'.2 H X P0 P (Real.sqrt X) Sg' m hHB hP2 hFin hSg hm.1 hm.2 hU2
  exact le_trans (norm_sub_le_norm_sub_add_norm_sub _ _ _) (add_le_add hb1 hb2)

end LeanLab.Pintz2021.DecompJ834
