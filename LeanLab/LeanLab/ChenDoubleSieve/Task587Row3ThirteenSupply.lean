import LeanLab.ChenDoubleSieve.Task587Row3ThirteenCertificate
import LeanLab.ChenDoubleSieve.Task587KernelFive
import LeanLab.ChenDoubleSieve.Task562Boxes

/-!
Tail supply for Wu 2004 Lemma 5.2 page 26, D2,13 at Table 1 row four page 30.
Source: https://arxiv.org/abs/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- Every row four D2,13 tail argument is at least five.
Wu 2004 page 26, derived endpoint calculation. -/
theorem r3Thirteen_tail_argument {φ : ℝ} (hφ : (16 / 5 : ℝ) ≤ φ) {x : Fin 3 → ℝ}
    (hx : x ∈ domain r3ThirteenLo r3ThirteenHi) : 5 ≤ (φ - ∑ j, x j) / x 1 := by
  have hu (j : Fin 3) : x j ≤ (2 / 5 : ℝ) := by
    have h := (hx.2 j).2
    fin_cases j <;> norm_num [r3ThirteenHi] at h ⊢ <;> linarith
  apply Task562.argument_ge_of_box (1 : Fin 3) (lo := r3ThirteenLo)
    (hi := fun _ => (2 / 5 : ℝ)) (P := 16 / 5) (by norm_num)
    ⟨fun j => (hx.2 j).1, hu⟩ (by
      have h := (hx.2 1).1
      norm_num [r3ThirteenLo] at h
      linarith) hφ
  norm_num

/-- The original rational bound holds throughout the unbounded phi tail.
Wu 2004 page 26, D2,13 at Table 1 row four page 30. -/
theorem r3Thirteen_integral_tail {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {φ : ℝ} (hφ : (16 / 5 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 r3ThirteenLo r3ThirteenHi φ ≤ (8106273 / 1000000000 : ℝ) := by
  have hlo (j : Fin 3) : 0 < r3ThirteenLo j := by fin_cases j <;> norm_num [r3ThirteenLo]
  have h := integral_le_poly_of_argument_five hω r3ThirteenLo r3ThirteenHi φ hlo
    r3ThirteenPoly r3ThirteenPoly_integrable (fun x hx => r3Thirteen_reciprocal_le_poly hx)
    (fun x hx => r3Thirteen_tail_argument hφ hx)
  have hc := mul_le_mul_of_nonneg_left r3Thirteen_polynomial_certificate
    (by norm_num : (0 : ℝ) ≤ 562 / 1000)
  exact h.trans (hc.trans (by norm_num))

/-- A concrete D2,13 point has phi two argument outside the initial Buchstab interval.
Wu 2004 page 26, derived obstruction to reusing the D2,16 initial-formula reduction. -/
theorem r3Thirteen_argument_witness :
    (![13 / 50, 8 / 25, 19 / 50] : Fin 3 → ℝ) ∈ domain r3ThirteenLo r3ThirteenHi ∧
    (2 - ∑ j : Fin 3, (![13 / 50, 8 / 25, 19 / 50] : Fin 3 → ℝ) j) /
      (![13 / 50, 8 / 25, 19 / 50] : Fin 3 → ℝ) 1 = (13 / 4 : ℝ) := by
  constructor
  · constructor
    · rw [Fin.monotone_iff_le_succ]
      intro j
      fin_cases j <;> norm_num
    · intro j
      fin_cases j <;> norm_num [r3ThirteenLo, r3ThirteenHi]
  · norm_num [Fin.sum_univ_succ]

end LeanLab.ChenDoubleSieve.Task587
