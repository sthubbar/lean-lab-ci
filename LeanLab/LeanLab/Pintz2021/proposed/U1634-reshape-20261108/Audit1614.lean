/-
Unit U-1614, run 20261104T0803Z-26516. Old `leaf_P_exists` at large `ε`, and the universal constant
form of the main term leaf of `DecompJ803`, `DecompJ834`. The negative `ε` case and the `m = 0` case are
`DecompJ665.P_leaf_false` and `DecompJ665.singular_series_leaf_false`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
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

namespace LeanLab.Pintz2021.Audit1614

/-- The old `leaf_P_exists` is false also for positive `ε`: `ε = 1`, `X = 1/2`, `P₀ = 1`, `H = -1` make
`Thm1Hyp_v2` true, and `P₀ X^{-ε} = 2 > P₀`. So `ε < 4/9` is needed, not only `0 < ε`. -/
theorem old_leaf_P_exists_large_eps_false :
    ¬ ∀ {ε H0 X0 H X P0 : ℝ}, 0 < ε → Thm1Hyp_v2 ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧ (excSet H (Real.sqrt X) P X).Finite := by
  intro h
  have hl : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hyp : Thm1Hyp_v2 1 (-1) 0 (-1) (1 / 2) 1 := by
    refine ⟨le_rfl, ?_, by norm_num, le_rfl, ?_⟩
    · rw [hl]; linarith [Real.log_two_lt_d9]
    · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨P, h1, h2, -⟩ := h one_pos hyp
  have : ((1 / 2 : ℝ)) ^ (-(1 : ℝ)) = 2 := by
    rw [Real.rpow_neg_one]; norm_num
  rw [this] at h1
  linarith

/-- If the singular series of `leaf_singular_series_converges_2` converge at the instance, the
`leaf_main_term_bound_exists_C_2` form, also `_3`, fails with `C = -1`: a norm is not negative. -/
theorem old_leaf_main_term_bound_exists_C_false_of_converges
    (hc : ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
      ∀ z ∈ excSet 0 (Real.sqrt 4) 1 4, ∀ w ∈ excSet 0 (Real.sqrt 4) 1 4, ∀ m : ℕ, 0 < m →
        Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) :
    ¬ ∀ (ε ε0 c H0 C X0 : ℝ), ∀ H X P0 P : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ,
      Thm1Hyp_v2 ε H0 X0 H X P0 → P0 * X ^ (-ε) ≤ P → P ≤ P0 →
      (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
        Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) →
      ∀ m : ℕ, (m : ℝ) ≤ X → 0 < m →
        ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
          C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by
  intro h
  obtain ⟨Sg', hSg⟩ := hc
  have hyp : Thm1Hyp_v2 0 0 0 0 4 1 := by
    refine ⟨le_rfl, ?_, by norm_num, le_rfl, ?_⟩
    · exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
    · exact Real.one_le_rpow (by norm_num) (by norm_num)
  have := h 0 0 0 0 (-1) 0 0 4 1 1 Sg' hyp (by simp) le_rfl hSg 1 (by norm_num) one_pos
  have hS : 0 < Sing 1 := lt_of_lt_of_le (by linarith [LeanLab.Pintz2021.Applications.C0_pos]) (LeanLab.Pintz2021.Applications.two_C0_le_Sing' 1)
  have hr : (0 : ℝ) < (4 : ℝ) ^ ((1 : ℝ) - 0) := by positivity
  have hn := norm_nonneg (R1majPrime 0 4 1 1 - mainTermPrime (excSet 0 (Real.sqrt 4) 1 4) Sg' 0 4 1)
  have he : (0 : ℝ) < Real.exp (-(0 * 0)) := Real.exp_pos _
  nlinarith [mul_pos (mul_pos hS (by norm_num : (0 : ℝ) < 4)) he]

end LeanLab.Pintz2021.Audit1614
#print axioms LeanLab.Pintz2021.Audit1614.old_leaf_P_exists_large_eps_false
#print axioms LeanLab.Pintz2021.Audit1614.old_leaf_main_term_bound_exists_C_false_of_converges
