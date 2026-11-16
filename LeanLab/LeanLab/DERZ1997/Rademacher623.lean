import LeanLab.DERZ1997.Decomp576a

/-!
Rademacher 1959, printed pages 198 and 199, displays 6.1 and 6.2 and Theorem 3.
The full strip theorem remains a cited input. Its right boundary is proved here.
The transfer retains the printed modulus restriction explicitly.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.DERZ1997.Rademacher623
open Complex
open Decomp576a.Decomp576aWip

/-- Rademacher printed page 198, display 6.1.
The estimate holds for every character, without primitivity.
-/
theorem right_boundary623 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    ‖DirichletCharacter.LFunction χ ((1 + η : ℝ) + (t : ℂ) * I)‖ ≤
      (riemannZeta ((1 + η : ℝ) : ℂ)).re := by
  have hs : 1 < (((1 + η : ℝ) : ℂ) + (t : ℂ) * I).re := by
    simpa only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero] using (show 1 < 1 + η by linarith)
  simpa only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
    zero_mul, sub_zero, add_zero] using LFunction_norm_le_zeta χ hs

/-- The right boundary of the exact printed Theorem 3 has exponent zero.
Rademacher printed page 199, unnumbered display following 6.2.
-/
theorem convexity_right_boundary623 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {η : ℝ} (hη : 0 < η) (s : ℂ)
    (hs : s.re = 1 + η) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      ((q : ℝ) * ‖s + 1‖ / (2 * Real.pi)) ^ ((1 + η - s.re) / 2) *
        (riemannZeta ((1 + η : ℝ) : ℂ)).re := by
  rw [hs, sub_self, zero_div, Real.rpow_zero, one_mul]
  simpa only [hs] using LFunction_norm_le_zeta χ (by linarith : 1 < s.re)

/-- CONDITIONAL ON the positive-eta part of the printed Rademacher Theorem 3.
The printed modulus restriction follows from the lab's nonprincipal premise.
No analytic interpolation is proved by this transport.
-/
theorem primitive_convexity_of_printed623
    (hRad : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      1 < q → χ.IsPrimitive → ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      ∀ s : ℂ, -η ≤ s.re → s.re ≤ 1 + η →
      ‖DirichletCharacter.LFunction χ s‖ ≤
        ((q : ℝ) * ‖1 + s‖ / (2 * Real.pi)) ^ ((1 + η - s.re) / 2) *
          (riemannZeta ((1 + η : ℝ) : ℂ)).re)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) (s : ℂ)
    (hs0 : -η ≤ s.re) (hs1 : s.re ≤ 1 + η) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      ((q : ℝ) * ‖s + 1‖ / (2 * Real.pi)) ^ ((1 + η - s.re) / 2) *
        (riemannZeta ((1 + η : ℝ) : ℂ)).re := by
  have hq0 : 0 < q := NeZero.pos q
  have hq1 : q ≠ 1 := fun h => hne (DirichletCharacter.level_one' χ h)
  have hq : 1 < q := by omega
  simpa only [add_comm (1 : ℂ) s] using hRad q χ hq hχ η hη0 hη1 s hs0 hs1

end LeanLab.DERZ1997.Rademacher623
