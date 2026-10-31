/-
The complex power Taylor step on page 29 in the proof of display 7.20.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Taylor107

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF. Page 29 proof of 7.20. A uniform mean value bound on the effective positive support. -/
theorem cpow_near_one107 {x : ℝ} (hx : x ∈ Set.Icc (2 / 5 : ℝ) (8 / 5))
    {z : ℂ} (hzre : -1 ≤ z.re ∧ z.re ≤ 1) :
    ‖(x : ℂ) ^ z - 1‖ ≤ (25 / 4 : ℝ) * ‖z‖ * |x - 1| := by
  by_cases hz : z = 0
  · simp [hz]
  have hder : ∀ t ∈ Set.Icc (2 / 5 : ℝ) (8 / 5),
      HasDerivWithinAt (fun u : ℝ => (u : ℂ) ^ z)
        (z * (t : ℂ) ^ (z - 1)) (Set.Icc (2 / 5 : ℝ) (8 / 5)) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact (hasDerivAt_ofReal_cpow_const ht0.ne' hz).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (2 / 5 : ℝ) (8 / 5),
      ‖z * (t : ℂ) ^ (z - 1)‖ ≤ (25 / 4 : ℝ) * ‖z‖ := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
    have hp : t ^ (z.re - 1) ≤ (25 / 4 : ℝ) := by
      calc
        _ ≤ (2 / 5 : ℝ) ^ (z.re - 1) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) ht.1 (by linarith [hzre.2])
        _ ≤ (2 / 5 : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith [hzre.1])
        _ = _ := by norm_num [Real.rpow_neg, Real.rpow_two]
    nlinarith [mul_le_mul_of_nonneg_left hp (norm_nonneg z)]
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc _ _)
    (show (1 : ℝ) ∈ Set.Icc (2 / 5 : ℝ) (8 / 5) by norm_num) hx
  simpa only [Complex.ofReal_one, Complex.one_cpow, Real.norm_eq_abs] using hm

/-- LEAF. Page 29 proof of 7.20. The exponent norm is controlled by one plus the sum frequency. -/
theorem sum_exponent_norm107 {ρ₁ ρ₂ : ℂ} (h₁ : 0 < ρ₁.re) (h₁' : ρ₁.re ≤ 1)
    (h₂ : 0 < ρ₂.re) (h₂' : ρ₂.re ≤ 1) :
    ‖ρ₁ + ρ₂ - 1‖ ≤ 1 + |(ρ₁ + ρ₂).im| := by
  have hre : |(ρ₁ + ρ₂ - 1).re| ≤ 1 := by
    rw [abs_le]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
    constructor <;> linarith
  have hi : (ρ₁ + ρ₂ - 1).im = (ρ₁ + ρ₂).im := by simp
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by rw [hi]; linarith)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.cpow_near_one107
#print axioms LeanLab.BhowmikGrimmelt2026.sum_exponent_norm107
