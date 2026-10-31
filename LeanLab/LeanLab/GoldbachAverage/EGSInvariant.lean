import LeanLab.GoldbachAverage.GSTheorem1

/-!
P0051, arXiv 2110.14250v2, eq. 12 page 3.
The value of E is independent of the admissible radius and is real.
These consequences use the proved coefficient identity, not a cited input.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage
open Finset Complex

/-- The radius in eq. 12 does not change E. -/
theorem EGS_radius_independent (N : ℕ) {r s : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    EGS N r = EGS N s := by
  rw [EGS_eq N hr0 hr1, EGS_eq N hs0 hs1]

/-- The coefficients of the error series are real. -/
lemma dc_im_zero (n : ℕ) : (dc n).im = 0 := by
  simp only [dc, Complex.im_sum]
  apply sum_eq_zero
  intro p _hp
  by_cases h1 : p.1 = 0 <;> by_cases h2 : p.2 = 0 <;>
    simp [cf, h1, h2, Complex.mul_im]

/-- The integral in eq. 12 is real despite its complex integrand. -/
theorem EGS_im_zero (N : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (EGS N r).im = 0 := by
  rw [EGS_eq N hr0 hr1, Complex.im_sum]
  simp only [dc_im_zero, sum_const_zero]

/-- Concrete admissible radii for the invariance statement. -/
theorem EGS_radius_at_two : EGS 2 (1 / 2) = EGS 2 (1 / 3) := by
  exact EGS_radius_independent 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Concrete instance of the reality statement. -/
theorem EGS_real_at_two : (EGS 2 (1 / 2)).im = 0 :=
  EGS_im_zero 2 (by norm_num) (by norm_num)

end LeanLab.GoldbachAverage
