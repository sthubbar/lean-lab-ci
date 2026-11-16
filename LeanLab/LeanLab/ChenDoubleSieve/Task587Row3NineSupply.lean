import LeanLab.ChenDoubleSieve.Task587Tail
import LeanLab.ChenDoubleSieve.Task587Row3NineIdentity
import LeanLab.ChenDoubleSieve.Task562Boxes

/-!
Unbounded phi tail supply for Wu 2004 Lemma 5.2 page 26, D2,9.
Source: https://arxiv.org/abs/0705.1652, Table 1 row four page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- At phi at least fourteen fifths every argument is at least four.
Wu 2004 page 26, D2,9 at Table 1 row four. -/
theorem r3Nine_tail_argument {φ : ℝ} (hφ : (14 / 5 : ℝ) ≤ φ) {x : Fin 3 → ℝ}
    (hx : x ∈ domain (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ))) :
    4 ≤ (φ - ∑ j, x j) / x 1 := by
  apply Task562.argument_ge_of_box (1 : Fin 3)
    (lo := fun _ => (25 / 89 : ℝ)) (hi := fun _ => (2 / 5 : ℝ))
    (P := 14 / 5) (by norm_num) ⟨fun j => (hx.2 j).1, fun j => (hx.2 j).2⟩
    (lt_of_lt_of_le (by norm_num) (hx.2 1).1) hφ
  norm_num

/-- The unbounded phi tail is below the original rational budget.
Wu 2004 page 26, D2,9 at Table 1 row four page 30. -/
theorem r3Nine_integral_tail {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {φ : ℝ} (hφ : (14 / 5 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) φ ≤
      (12408337 / 1000000000 : ℝ) := by
  have hi := Wu04I1.I1_integrable hω (s := (5 / 2 : ℝ))
    (by norm_num) (by norm_num : (0 : ℝ) < 89 / 25) (by linarith : 2 ≤ φ)
  norm_num at hi
  have hk := Wu04I1.reciprocal_integrable (s := (5 / 2 : ℝ))
    (by norm_num : (0 : ℝ) < 89 / 25)
  norm_num at hk
  have hm := setIntegral_mono_on hi (hk.const_mul (563 / 1000 : ℝ))
    (Wu04I1.domain_isCompact _ _).measurableSet (fun x hx => by
      have hw := buchstab_le_563 hω (r3Nine_tail_argument hφ hx)
      have hp : 0 < (∏ j, x j) * x 1 :=
        mul_pos (prod_pos fun j _ => lt_of_lt_of_le (by norm_num) (hx.2 j).1)
          (lt_of_lt_of_le (by norm_num) (hx.2 1).1)
      simpa only [Wu04I1.reciprocal, mul_one_div] using
        div_le_div_of_nonneg_right hw hp.le)
  rw [MeasureTheory.integral_const_mul] at hm
  have hpoly := r3Nine_integral_le_poly.trans r3Nine_polynomial_certificate
  have hbound := mul_le_mul_of_nonneg_left hpoly (by norm_num : (0 : ℝ) ≤ 563 / 1000)
  exact hm.trans (hbound.trans (by norm_num))

/-- A concrete ordered point witnesses the polynomial cell and both phi ranges.
Wu 2004 page 26, D2,9 at Table 1 row four. -/
theorem r3Nine_cell_instance :
    (fun _ : Fin 3 => (1 / 3 : ℝ)) ∈
      domain (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) ∧
    (2 : ℝ) < 14 / 5 ∧ (14 / 5 : ℝ) < 3 := by
  refine ⟨⟨monotone_const, ?_⟩, ?_, ?_⟩ <;> norm_num

end LeanLab.ChenDoubleSieve.Task587
