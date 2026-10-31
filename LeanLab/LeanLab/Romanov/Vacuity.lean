import LeanLab.Romanov.GallagherBridge
import LeanLab.Romanov.GapMean
import LeanLab.Romanov.WeightedMean

/-!
# Concrete instances for task65 statements

AI wrote the Lean code. These are definition checks for the twins in STATEMENTS.md.
They are not finite range claims about primes. Binary Goldbach is OPEN.
-/

namespace LeanLab.Romanov

open Finset

/-- Positive exponents count different pairs from the unrestricted finite fiber. -/
theorem task65_count_instances :
    repCount 0 = 0 ∧ repCount 4 = 1 ∧ repCount 7 = 2 ∧
      fiberCount {(2, 1), (3, 0)} 4 = 2 ∧ coll {(2, 1), (3, 0)} = 4 ∧
      coll (primeBox 1) = 2 := by decide

/-- Nonzero instances of the singular and Mersenne weights. -/
theorem task65_weight_instances :
    LeanLab.SchnirelmannGoldbach.singProd 2 = (3 : ℝ) / 2 ∧
      (LeanLab.HeathBrownPuchta.Lemma8Const.h 1 : ℝ) = 1 ∧
      (LeanLab.HeathBrownPuchta.Lemma8Const.h 3 : ℝ) = 2 ∧
      (∑ l ∈ Icc 1 2, ((2 - l : ℕ) : ℝ) *
        (LeanLab.HeathBrownPuchta.Lemma8Const.h (2 ^ l - 1) : ℝ)) = 1 := by
  constructor
  · norm_num [LeanLab.SchnirelmannGoldbach.singProd]
  constructor
  · exact_mod_cast LeanLab.HeathBrownPuchta.Lemma8Const.h1
  constructor
  · have hh := LeanLab.HeathBrownPuchta.Lemma8Const.h2
    norm_num at hh
    exact_mod_cast hh
  · norm_num [show Icc 1 2 = ({1, 2} : Finset ℕ) by decide,
      LeanLab.HeathBrownPuchta.Lemma8Const.h1, LeanLab.HeathBrownPuchta.Lemma8Const.h2]

/-- A nonempty small G arc instance has exact cancellation at one quarter. -/
theorem task65_arc_cancellation :
    LeanLab.Linnik.U1426ChainWire.Gs 2 (1 / 4) = 0 := by
  have hhalf : LeanLab.Linnik.U1412Display53.eC (1 / 2) = -1 := by
    have harg : (2 : ℂ) * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) =
        (Real.pi : ℂ) * Complex.I := by push_cast; ring
    unfold LeanLab.Linnik.U1412Display53.eC
    rw [harg, Complex.exp_pi_mul_I]
  have hone : LeanLab.Linnik.U1412Display53.eC 1 = 1 := by
    simp [LeanLab.Linnik.U1412Display53.eC, Complex.exp_two_pi_mul_I]
  norm_num [LeanLab.Linnik.U1426ChainWire.Gs,
    show Icc 1 2 = ({1, 2} : Finset ℕ) by decide, hhalf, hone]

/-- The small G hypothesis holds on an interval of positive length. -/
theorem task65_small_arc_interval : ∃ δ : ℝ, 0 < δ ∧
    Set.Icc (1 / 4 - δ) (1 / 4 + δ) ⊆ Set.Icc (0 : ℝ) 1 ∧
    ∀ α ∈ Set.Icc (1 / 4 - δ) (1 / 4 + δ),
      ‖LeanLab.Linnik.U1426ChainWire.Gs 2 α‖ ≤ (1 - Real.log 2 / 2) * 2 := by
  set M : ℝ := (1 - Real.log 2 / 2) * 2
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hM : 0 < M := by dsimp [M]; norm_num at hlog; linarith
  have hc : ContinuousAt (fun α : ℝ => ‖LeanLab.Linnik.U1426ChainWire.Gs 2 α‖) (1 / 4) :=
    (LeanLab.Linnik.U1426ChainWire.continuous_Gs 2).norm.continuousAt
  obtain ⟨r, hr, hclose⟩ := Metric.continuousAt_iff.mp hc M hM
  set δ := min (r / 2) (1 / 8 : ℝ)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ8 : δ ≤ 1 / 8 := min_le_right _ _
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro α hα
    constructor <;> linarith [hα.1, hα.2]
  · intro α hα
    have hdist : dist α (1 / 4 : ℝ) < r := by
      rw [Real.dist_eq]
      apply lt_of_le_of_lt (abs_le.mpr ⟨by linarith [hα.1], by linarith [hα.2]⟩) hδr
    have hb := hclose hdist
    have hc0 : ‖LeanLab.Linnik.U1426ChainWire.Gs 2 (1 / 4)‖ = 0 := by
      rw [task65_arc_cancellation, norm_zero]
    rw [hc0, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
    exact hb.le

end LeanLab.Romanov
