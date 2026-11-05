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

namespace LeanLab.Pintz2021.DecompJ803

/-- REFUTED, `DecompJ665.P_leaf_false`, no `0 < ε`. Repaired in `DecompJ579.leaf_P_exists`. Do not prove this.
LEAF arXiv:1804.05561v1 display 8.28: the major arc parameter P exists -/
theorem leaf_P_exists_2 {ε H0 X0 H X P0 : ℝ} (hHyp : Thm1Hyp ε H0 X0 H X P0) :
  ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧ (excSet H (Real.sqrt X) P X).Finite := by sorry

/-- LEAF arXiv:1804.05561v1 display 9.16: the singular series converges -/
theorem leaf_singular_series_converges_2 (H X P : ℝ) :
  ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m)) := by sorry

/-- REFUTED given `leaf_singular_series_converges_2`, `Audit1614.old_leaf_main_term_bound_exists_C_false_of_converges`: `C` is universal, take `C = -1`. Use `DecompJ579.leaf_main_term_bound`. Do not prove this.
LEAF arXiv:1804.05561v1 display 10.25: the main term error is bounded by a constant C depending only on ε -/
theorem leaf_main_term_bound_exists_C_2 (ε ε0 c H0 C X0 : ℝ) :
  ∀ H X P0 P : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    Thm1Hyp ε H0 X0 H X P0 →
    P0 * X ^ (-ε) ≤ P → P ≤ P0 →
    (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) →
    ∀ m : ℕ, (m : ℝ) ≤ X → 0 < m →
      ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
        C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by sorry

/-- LEAF arXiv:1804.05561v1 display 8.28: the epsilon threshold and core constants exist -/
theorem leaf_constants_exist_2 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c := by
  exact ⟨1, one_pos, fun _ _ _ => ⟨1, 0, 0, 0, one_pos⟩⟩

/-- Assembly of Theorem 1 display 2.21 (untruncated form). -/
theorem assembly_221_2 :
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
  obtain ⟨ε0, hε0, h1⟩ := leaf_constants_exist_2
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hε0'
  obtain ⟨c, H0, C, X0, hc⟩ := h1 ε hε hε0'
  refine ⟨c, H0, C, X0, hc, ?_⟩
  intro H X P0 hHyp
  obtain ⟨P, hP1, hP2, hFin⟩ := leaf_P_exists_2 hHyp
  refine ⟨P, hP1, hP2, hFin, ?_⟩
  obtain ⟨Sg', hSg1⟩ := leaf_singular_series_converges_2 H X P
  refine ⟨Sg', hSg1, ?_⟩
  exact leaf_main_term_bound_exists_C_2 ε ε0 c H0 C X0 H X P0 P Sg' hHyp hP1 hP2 hSg1

/- REPAIRED 2026-11-05 lomos 20261105T1214Z: `1 ≤ P` added, the only change of statement in this
file. The former form assumed only `P ≤ P0`, and `DecompJ665.truncation_leaf281_false` (also
`DecompJ281Audit.leaf_truncation_error_false`) is a kernel-checked negation of it: at the level
`P = 0` the exceptional set is the pole alone, the truncated sum vanishes at every cutoff `U`
because `Nat.lcm pole.r pole.r = 1 > P`, the full sum keeps the pole term, and the right hand side
`C' * (Sing m * X * log U / sqrt U)` tends to zero as `U → ∞`, so no constant exists. The lower
bound `1 ≤ P` is the paper's own requirement that the pole pair survive the `[r₁, r₂] ≤ P`
restriction (`DecompJ281.pole_lcm_retained`), and `assembly_222_2` supplies it at `P = P0`, which
lies in `[P0 X^{-ε}, P0]` once `X ≥ 1` because `Thm1Hyp` gives `1 ≤ P0`. The leaf itself stays
OPEN: display 10.27 needs the mass of the discarded pairs, which is not in Mathlib. -/
/-- LEAF arXiv:1804.05561v1 display 10.27: the truncated tail error is bounded -/
theorem leaf_truncation_error_2 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ H0 C' X0 : ℝ, 0 < C' ∧ ∀ H X P0 P U : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ, ∀ m : ℕ,
      Thm1Hyp ε H0 X0 H X P0 → 1 ≤ P → P ≤ P0 →
      (excSet H (Real.sqrt X) P X).Finite →
      (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ n : ℕ, 0 < n →
        Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg' z w n))) →
      X / 4 ≤ m → (m : ℝ) ≤ X / 2 → 2 ≤ U →
      ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
        mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
      C' * (Sing m * X * Real.log U / Real.sqrt U) := by sorry

/-- LEAF Assembly of Theorem 1 display 2.22 (truncated form). -/
theorem assembly_222_2 :
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
  obtain ⟨εc, hεc, hconst⟩ := leaf_constants_exist_2
  obtain ⟨εt, hεt, htrunc⟩ := leaf_truncation_error_2
  refine ⟨min εc εt, lt_min hεc hεt, ?_⟩
  intro ε hε hεlt
  obtain ⟨c, H0a, Ca, X0a, hc⟩ := hconst ε hε (lt_of_lt_of_le hεlt (min_le_left _ _))
  obtain ⟨H0b, C', X0b, hC'⟩ := htrunc ε hε (lt_of_lt_of_le hεlt (min_le_right _ _))
  refine ⟨c, max H0a H0b, Ca, C', max (max X0a X0b) 4, hc, ?_⟩
  intro H X P0 hHyp
  obtain ⟨hH0, hHlog, hX0, hP01, hP0X⟩ := hHyp
  have hXa : X0a ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX0
  have hXb : X0b ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX0
  have hX4 : (4 : ℝ) ≤ X := le_trans (le_max_right _ _) hX0
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hHA : Thm1Hyp ε H0a X0a H X P0 :=
    ⟨le_trans (le_max_left _ _) hH0, hHlog, hXa, hP01, hP0X⟩
  have hHB : Thm1Hyp ε H0b X0b H X P0 :=
    ⟨le_trans (le_max_right _ _) hH0, hHlog, hXb, hP01, hP0X⟩
  -- the level `P = P0` lies in `[P0 X^{-ε}, P0]`, and it is at least `1`, as the repaired
  -- truncation leaf requires and `Thm1Hyp` supplies
  have hlow : P0 * X ^ (-ε) ≤ P0 := by
    have hx : X ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
    calc P0 * X ^ (-ε) ≤ P0 * 1 := mul_le_mul_of_nonneg_left hx (by linarith)
      _ = P0 := mul_one P0
  have hFin : (excSet H (Real.sqrt X) P0 X).Finite := excSet_finite H (Real.sqrt X) P0 X
  obtain ⟨Sg', hSg⟩ := leaf_singular_series_converges_2 H X P0
  refine ⟨P0, hlow, le_rfl, hFin, Sg', hSg, ?_⟩
  intro m hm
  have hmX : (m : ℝ) ≤ X := by linarith [hm.2]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith [hm.1]
  have hmpos : 0 < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
  have hU2 : (2 : ℝ) ≤ Real.sqrt X := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hX4
  have hb1 := leaf_main_term_bound_exists_C_2 ε (min εc εt) c H0a Ca X0a H X P0 P0 Sg' hHA
    hlow le_rfl hSg m hmX hmpos
  have hb2 := hC'.2 H X P0 P0 (Real.sqrt X) Sg' m hHB hP01 le_rfl hFin hSg hm.1 hm.2 hU2
  exact le_trans (norm_sub_le_norm_sub_add_norm_sub _ _ _) (add_le_add hb1 hb2)

end LeanLab.Pintz2021.DecompJ803
