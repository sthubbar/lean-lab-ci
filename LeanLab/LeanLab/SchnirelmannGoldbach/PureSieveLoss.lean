/-
The loss of the original pure Brun bound in the Goldbach density step.
Brun 1919, page 127, display 12 has a cubed log-log loss.
Squaring that loss in the second-moment estimate gives a sixth power.
This only diagnoses the lower coefficient supplied by that estimate.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.SchnirelmannGoldbach.BrunRatio

open Filter
open scoped Topology

namespace LeanLab.SchnirelmannGoldbach.PureSieve

/-- The sixth-power reciprocal log-log coefficient tends to zero. -/
theorem brun_loss_tendsto_zero :
    Tendsto (fun x : ℝ => 1 / (Real.log (Real.log x)) ^ 6) atTop (𝓝 0) := by
  have htop : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hinv : Tendsto (fun x : ℝ => (Real.log (Real.log x))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htop
  simpa only [one_div, inv_pow, zero_pow (by norm_num : 6 ≠ 0)] using hinv.pow 6

/-- The original loss coefficient cannot itself give a uniform positive lower coefficient. -/
theorem brun_loss_not_uniform :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x : ℝ in atTop,
      δ ≤ 1 / (Real.log (Real.log x)) ^ 6 := by
  rintro ⟨δ, hδ, hlower⟩
  have hsmall : ∀ᶠ x : ℝ in atTop, 1 / (Real.log (Real.log x)) ^ 6 < δ :=
    brun_loss_tendsto_zero.eventually (gt_mem_nhds hδ)
  obtain ⟨x, hle, hlt⟩ := (hlower.and hsmall).exists
  exact (not_lt_of_ge hle) hlt

end LeanLab.SchnirelmannGoldbach.PureSieve

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.brun_loss_tendsto_zero

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.brun_loss_not_uniform
