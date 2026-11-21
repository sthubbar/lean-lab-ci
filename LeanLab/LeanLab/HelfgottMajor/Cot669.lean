import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
The elementary cotangent factor of P0014 page 34 after display 4.10.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Cot669
open Complex
open scoped ComplexConjugate

/-- P0014 page 34 after display 4.10. Cotangent has norm one on the quarter pi line. -/
theorem norm_cot_quarter (τ : ℝ) :
    ‖cot (((Real.pi / 4 : ℝ) : ℂ) + τ * I)‖ = 1 := by
  let z : ℂ := ((Real.pi / 4 : ℝ) : ℂ) + τ * I
  have hz : (Real.pi : ℂ) / 2 - z = conj z := by
    dsimp [z]
    simp only [map_add, map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  have hc : cos z = conj (sin z) := by
    rw [← sin_pi_div_two_sub, hz, sin_conj]
  have hs : sin z ≠ 0 := by
    intro h
    have ht := sin_sq_add_cos_sq z
    simp [hc, h] at ht
  change ‖cot z‖ = 1
  rw [cot_eq_cos_div_sin, norm_div, hc, norm_conj, div_self (norm_ne_zero_iff.mpr hs)]

/-- P0014 page 34 after display 4.10. The gamma reflection cotangent factor has norm one
on real part minus one half, for both possible parities. -/
theorem norm_cot_reflection (τ : ℝ) (κ : ℕ) (hκ : κ = 0 ∨ κ = 1) :
    ‖cot ((Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + κ) / 2)‖ = 1 := by
  rcases hκ with rfl | rfl
  · have he : (Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + (0 : ℕ)) / 2 =
        -(((Real.pi / 4 : ℝ) : ℂ) + (-Real.pi * τ / 2 : ℝ) * I) := by
      push_cast
      ring
    rw [he, cot_eq_cos_div_sin, cos_neg, sin_neg, div_neg, norm_neg,
      ← cot_eq_cos_div_sin]
    exact norm_cot_quarter _
  · have he : (Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + (1 : ℕ)) / 2 =
        ((Real.pi / 4 : ℝ) : ℂ) + (Real.pi * τ / 2 : ℝ) * I := by
      push_cast
      ring
    rw [he]
    exact norm_cot_quarter _

end LeanLab.HelfgottMajor.Cot669

#print axioms LeanLab.HelfgottMajor.Cot669.norm_cot_quarter
#print axioms LeanLab.HelfgottMajor.Cot669.norm_cot_reflection
