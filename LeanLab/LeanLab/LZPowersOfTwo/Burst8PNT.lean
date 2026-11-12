/-
ROUTE BURST session 8, part 2: the prime number theorem input for display (26) of P0079.
AI wrote this Lean code. Binary Goldbach is OPEN; this file says nothing about it.

`θ(x) / x → 1`, derived from the lab's sorry-free port `LeanLab.PNTPort.StrongPNT.MediumPNT`
of the PrimeNumberTheoremAnd project, and Mathlib's `ψ - θ = O(√x)`.
-/
import LeanLab.PNTPort.StrongPNT.MediumPNT

open Real Filter Asymptotics
open scoped Chebyshev
noncomputable section
namespace LeanLab.LZPowersOfTwo.Burst8P2

/-- `√x = o(x)`. -/
theorem sqrt_isLittleO_id_p2 : Real.sqrt =o[atTop] (fun x : ℝ => x) := by
  rw [isLittleO_iff_tendsto (fun x hx => by simp [hx])]
  have h : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (by
      simpa using (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr' (by
        filter_upwards [eventually_ge_atTop 0] with x hx
        rw [Real.sqrt_eq_rpow]))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  rw [eq_div_iff hx.ne']
  nth_rewrite 2 [← Real.mul_self_sqrt hx.le]
  field_simp

/-- The prime number theorem in the form `θ(x) / x → 1`. PROVED from the lab port
`MediumPNT` and Mathlib's `isBigO_psi_sub_theta_sqrt`. -/
theorem theta_div_tendsto_one_p2 :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  have hexp : Tendsto (fun x : ℝ => Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))
      atTop (nhds 0) := by
    apply tendsto_exp_atBot.comp
    apply Tendsto.const_mul_atTop_of_neg (by linarith)
    exact (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  have h1 : (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) =o[atTop]
      (fun x : ℝ => x) := by
    have := ((isLittleO_one_iff ℝ).mpr hexp).mul_isBigO (isBigO_refl (fun x : ℝ => x) atTop)
    simpa [mul_comm] using this
  have hpsi : (ψ - id) =o[atTop] (fun x : ℝ => x) := hO.trans_isLittleO h1
  have hpt : (ψ - θ) =o[atTop] (fun x : ℝ => x) :=
    Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO sqrt_isLittleO_id_p2
  have hth : (fun x : ℝ => θ x - x) =o[atTop] (fun x : ℝ => x) := by
    have := hpsi.sub hpt
    refine this.congr_left ?_
    intro x
    simp
  have ht := hth.tendsto_div_nhds_zero
  have := ht.add_const 1
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp
  ring

end LeanLab.LZPowersOfTwo.Burst8P2
