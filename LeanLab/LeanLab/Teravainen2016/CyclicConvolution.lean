/-
P0076, Section 2, pages 6 to 7. Convolution and its normalized Fourier transform.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.NormalizedFourier

open Finset
open scoped Classical ZMod

namespace LeanLab.Teravainen2016

noncomputable def cyclicConv {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) (x : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ y, f y * g (x - y)

/-- Convolution becomes multiplication with the normalized transform. -/
theorem normalizedDFT_conv {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) (ξ : ZMod N) :
    normalizedDFT (cyclicConv f g) ξ = normalizedDFT f ξ * normalizedDFT g ξ := by
  unfold normalizedDFT cyclicConv
  simp only [ZMod.dft_apply, smul_eq_mul]
  have h : ∑ x : ZMod N, ZMod.stdAddChar (-(x * ξ)) * ((N : ℂ)⁻¹ * ∑ y, f y * g (x - y)) =
      (N : ℂ)⁻¹ * ((∑ y, ZMod.stdAddChar (-(y * ξ)) * f y) *
        ∑ z, ZMod.stdAddChar (-(z * ξ)) * g z) := by
    rw [sum_mul_sum]
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro y _
    have ht : (∑ x : ZMod N, ZMod.stdAddChar (-(x * ξ)) *
        ((N : ℂ)⁻¹ * (f y * g (x - y)))) =
        ∑ z : ZMod N, ZMod.stdAddChar (-((z + y) * ξ)) *
          ((N : ℂ)⁻¹ * (f y * g (z + y - y))) := by
      exact (Fintype.sum_equiv (Equiv.addRight y) _ _ (fun z => rfl)).symm
    rw [ht]
    apply sum_congr rfl
    intro z _
    change ZMod.stdAddChar (-((z + y) * ξ)) * ((N : ℂ)⁻¹ * (f y * g (z + y - y))) = _
    rw [add_sub_cancel_right, add_mul, neg_add, AddChar.map_add_eq_mul]
    ring
  rw [h]
  ring

/-- Parseval followed by the convolution identity, page 7. -/
theorem cyclicConv_energy {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    (N : ℝ)⁻¹ * ∑ n, ‖cyclicConv f g n‖ ^ 2 =
      ∑ ξ, ‖normalizedDFT f ξ * normalizedDFT g ξ‖ ^ 2 := by
  rw [normalized_parseval (cyclicConv f g)]
  simp_rw [normalizedDFT_conv]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp

/-- Subtracting the smooth part subtracts its transform. -/
theorem normalizedDFT_sub {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) (ξ : ZMod N) :
    normalizedDFT (fun n => f n - g n) ξ = normalizedDFT f ξ - normalizedDFT g ξ := by
  unfold normalizedDFT
  rw [show (fun n => f n - g n) = f - g by rfl, map_sub]
  simp only [Pi.sub_apply]
  ring

example : cyclicConv (fun _ : ZMod 1 => (1 : ℂ)) (fun _ => 1) 0 = 1 := by
  simp [cyclicConv]

#print axioms normalizedDFT_conv
#print axioms cyclicConv_energy
#print axioms normalizedDFT_sub

end LeanLab.Teravainen2016
