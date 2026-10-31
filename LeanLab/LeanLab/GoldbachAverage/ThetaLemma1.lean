import LeanLab.GoldbachAverage.GSCorollary2
import LeanLab.GoldbachAverage.EGSInvariant
import LeanLab.GoldbachAverage.ThetaErrorMajorant

/-!
Theta version of the layer reduction for P0051, arXiv 2110.14250v2.
The target is Theorem 6 eq. 33 second half on page 6.
The page 20 route is recorded in PROGRESS.md by U-1350.
Source pages 4, 6, 19 and 20 were read in this run. The local mean square input remains named.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.ThetaLayers
open Complex Finset Filter MeasureTheory Set
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov LeanLab.LZCesaroShort

/-- Local mean square input for the theta layer reduction.
This is an explicit missing analytic input, not an asserted theorem. -/
def ThetaLemma1 (theta : ℝ) : Prop := ∃ K : ℝ, 0 ≤ K ∧
  ∀ N : ℕ, 2 ≤ N → ∀ ξ : ℝ, 1 / (N : ℝ) ≤ ξ → ξ ≤ 1 / 2 →
    ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2 ≤
      K * (N : ℝ) ^ (2 * theta) * ξ * (1 + Real.log N) ^ 4

/-- The layer sum costs one logarithm for any nonnegative power a. -/
theorem EGS_bound_of_local (a : ℝ) (ha : 0 ≤ a)
    (hlocal : ∃ K : ℝ, 0 ≤ K ∧
      ∀ N : ℕ, 2 ≤ N → ∀ ξ : ℝ, 1 / (N : ℝ) ≤ ξ → ξ ≤ 1 / 2 →
        ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2 ≤
          K * (N : ℝ) ^ a * ξ * (1 + Real.log N) ^ 4) :
    ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
      ‖EGS N (Real.exp (-(1 / (N : ℝ))))‖ ≤ K * (N : ℝ) ^ a * Real.log N ^ 5 := by
  obtain ⟨K, hK⟩ := Emajorant_bound_of_local a ha hlocal
  exact ⟨K, fun N hN => (norm_EGS_le_Emajorant N _).trans (hK N hN)⟩

/-- BHMS error estimate, CONDITIONAL ON the named theta mean square input. -/
theorem bhms_theorem6E_proved (hlocal : ThetaLemma1 Theta) : GSCor2.BHMSTheorem6E := by
  intro hlo _hhi
  obtain ⟨K, hK⟩ := EGS_bound_of_local (2 * Theta) (by linarith) hlocal
  refine ⟨K, fun N hN r hr0 hr1 => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have he0 : 0 < Real.exp (-(1 / (N : ℝ))) := Real.exp_pos _
  have he1 : Real.exp (-(1 / (N : ℝ))) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := one_div_pos.mpr hN0
    linarith
  rw [EGS_radius_independent N hr0 hr1 he0 he1]
  exact hK N hN

/-- Corollary 2, CONDITIONAL ON the same named input. -/
theorem gs_corollary2_of_theta_lemma1 (hlocal : ThetaLemma1 Theta) :
    type_of% gs_corollary2 :=
  GSCor2.gs_corollary2_of_bhms (bhms_theorem6E_proved hlocal)

/-- Theorem 6 eq. 33 for the actual nonnegative majorant, with the named local input. -/
theorem bhms_theorem6_majorant (hlocal : ThetaLemma1 Theta) :
    1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      Emajorant N (Real.exp (-(1 / (N : ℝ)))) ≤
        C * (N : ℝ) ^ (2 * Theta) * Real.log N ^ 5 := by
  intro hlo _hhi
  exact Emajorant_bound_of_local (2 * Theta) (by linarith) hlocal

end LeanLab.GoldbachAverage.ThetaLayers
