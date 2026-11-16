import LeanLab.ChenDoubleSieve.Task587Row3TenCertificate
import LeanLab.ChenDoubleSieve.Task587Kernel
import LeanLab.ChenDoubleSieve.Task562Boxes

/-!
Tail supply for Wu 2004 Lemma 5.2 page 26, D2,10 at Table 1 row four page 30.
Source: https://arxiv.org/abs/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- Every row four D2,10 tail argument is at least four.
Wu 2004 page 26, derived endpoint calculation. -/
theorem r3Ten_tail_argument {φ : ℝ} (hφ : (14 / 5 : ℝ) ≤ φ) {x : Fin 3 → ℝ}
    (hx : x ∈ domain r3TenLo r3TenHi) : 4 ≤ (φ - ∑ j, x j) / x 1 := by
  have hu (j : Fin 3) : x j ≤ (2 / 5 : ℝ) := by
    have h := (hx.2 j).2
    fin_cases j <;> norm_num [r3TenHi] at h ⊢ <;> linarith
  apply Task562.argument_ge_of_box (1 : Fin 3) (lo := r3TenLo)
    (hi := fun _ => (2 / 5 : ℝ)) (P := 14 / 5) (by norm_num)
    ⟨fun j => (hx.2 j).1, hu⟩ (by
      have h := (hx.2 1).1
      norm_num [r3TenLo] at h
      linarith) hφ
  norm_num

/-- The original rational bound holds throughout the unbounded phi tail.
Wu 2004 page 26, D2,10 at Table 1 row four page 30. -/
theorem r3Ten_integral_tail {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {φ : ℝ} (hφ : (14 / 5 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 r3TenLo r3TenHi φ ≤ (2710363 / 500000000 : ℝ) := by
  have hlo (j : Fin 3) : 0 < r3TenLo j := by fin_cases j <;> norm_num [r3TenLo]
  have h := integral_le_poly_of_argument_four hω r3TenLo r3TenHi φ hlo
    r3TenPoly r3TenPoly_integrable (fun x hx => r3Ten_reciprocal_le_poly hx)
    (fun x hx => r3Ten_tail_argument hφ hx)
  have hc := mul_le_mul_of_nonneg_left r3Ten_polynomial_certificate
    (by norm_num : (0 : ℝ) ≤ 563 / 1000)
  exact h.trans (hc.trans (by norm_num))

end LeanLab.ChenDoubleSieve.Task587
