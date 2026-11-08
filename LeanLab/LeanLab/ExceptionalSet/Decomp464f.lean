import LeanLab.ExceptionalSet.Decomp428d

/-!
P0082 page 366, distant frequency integral localization.
The scalar phase bound remains an explicit hypothesis.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp464f

open Real MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp Kfun calE eC)
open LeanLab.ExceptionalSet.Decomp404e

/-- P0082 page 366, distant frequency contribution to display 26.
This exact companion is conditional on the explicit phase bound hphase.
It proves the integral localization without any admitted analytic estimate. -/
theorem leaf_far_localization (γ δ κ : ℝ) (N : ℕ) (V : ℝ) (hV : 0 ≤ V)
    (hΔ : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1)
    (hphase : ∀ α ∈ truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
      ∀ β ∈ truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
        F γ N ^ (3 * δ - 1) < |α - β| → ‖phaseSum γ N (β - α)‖ ≤ V) :
    farMoment γ δ κ N ≤ V *
      (∫ α in truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
        ‖Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
          (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)‖) ^ 2 := by
  let X := F γ N
  let P := X ^ (6 * δ)
  let Δ := calE γ κ N ^ (-(1 / 8 : ℝ))
  let A := truncatedDomain P X
  let w : ℝ → ℝ := fun x => ‖Sp P X x ^ 2 * (Kfun Δ x : ℂ)‖
  have hw (x : ℝ) : 0 ≤ w x := norm_nonneg _
  have hsp : Continuous (Sp P X) := by unfold Sp eC; fun_prop
  have hc : Continuous w :=
    ((hsp.pow 2).mul (KernelTransform264.Kfun_continuous Δ)).norm
  have hi : IntegrableOn w A :=
    hc.integrableOn_Icc.mono_set Set.inter_subset_right
  have hinner (α : ℝ) (hα : α ∈ A) :
      (∫ β in A ∩ {β : ℝ | X ^ (3 * δ - 1) < |α - β|},
        w α * w β * ‖phaseSum γ N (β - α)‖) ≤
        V * w α * (∫ β in A, w β) := by
    have hib : IntegrableOn (fun β => V * w α * w β) A := hi.const_mul _
    calc
      _ ≤ ∫ β in A ∩ {β : ℝ | X ^ (3 * δ - 1) < |α - β|},
          V * w α * w β := by
        apply setIntegral_mono_of_nonneg
        · intro β hβ
          exact mul_nonneg (mul_nonneg (hw α) (hw β)) (norm_nonneg _)
        · intro β hβ
          have hp := hphase α hα β hβ.1 hβ.2
          calc
            w α * w β * ‖phaseSum γ N (β - α)‖ ≤ w α * w β * V :=
              mul_le_mul_of_nonneg_left hp (mul_nonneg (hw α) (hw β))
            _ = V * w α * w β := by ring
        · exact hib.mono_set Set.inter_subset_left
      _ ≤ ∫ β in A, V * w α * w β :=
        setIntegral_mono_set hib
          (Filter.Eventually.of_forall (fun β => mul_nonneg (mul_nonneg hV (hw α)) (hw β)))
          (Filter.Eventually.of_forall (fun β hβ => hβ.1))
      _ = _ := integral_const_mul _ _
  change (∫ α in A,
    ∫ β in A ∩ {β : ℝ | X ^ (3 * δ - 1) < |α - β|},
      w α * w β * ‖phaseSum γ N (β - α)‖) ≤ V * (∫ α in A, w α) ^ 2
  calc
    _ ≤ ∫ α in A, V * w α * (∫ β in A, w β) := by
      apply setIntegral_mono_of_nonneg
      · intro α hα
        exact integral_nonneg (fun β =>
          mul_nonneg (mul_nonneg (hw α) (hw β)) (norm_nonneg _))
      · exact hinner
      · exact (hi.const_mul V).mul_const _
    _ = _ := by
      rw [integral_mul_const, integral_const_mul]
      ring

end LeanLab.ExceptionalSet.Decomp464f
