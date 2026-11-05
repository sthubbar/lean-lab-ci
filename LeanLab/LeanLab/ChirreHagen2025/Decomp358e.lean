import LeanLab.ChirreHagen2025.Decomp272a

/-!
P0075 page 5 equation 2.11. Mathlib supplies the entire regular part of zeta
and the Taylor theorem. AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp358e
open Decomp272a

/-- P0075 page 5 equation 2.11, identification of the regular part.
Mathlib fills the removable singularity with Euler's constant. -/
theorem regularPart_eq (z : ℂ) : regularPart z = riemannZeta₀ (1 + z) := by
  by_cases hz : z = 0
  · simp [regularPart, hz]
  · simp [regularPart, riemannZeta₀, hz, show (1 : ℂ) + z ≠ 1 by simpa using hz,
      one_div]

/-- P0075 page 5 equation 2.11, the regular part is entire.
The entire function from Mathlib is translated by one. -/
theorem regularPart_entire : Differentiable ℂ regularPart := by
  simp_rw [show regularPart = fun z => riemannZeta₀ (1 + z) from funext regularPart_eq]
  exact differentiable_riemannZeta₀.comp (differentiable_const 1 |>.add differentiable_id)

/-- P0075 page 5 equation 2.11, Taylor convergence at every complex argument.
This reuses Mathlib's Taylor theorem for entire functions. -/
theorem regularPart_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => laurentCoeff n * z ^ n) (regularPart z) := by
  convert Complex.hasSum_taylorSeries_of_entire regularPart_entire 0 z using 1
  ext n
  simp [laurentCoeff, smul_eq_mul, div_eq_mul_inv]
  ring

/-- P0075 page 5 equation 2.11. Exact target statement from Decomp272a.
This identity is unconditional and has no cited coefficient estimate. -/
theorem laurent_series (t : ℝ) (ht : 0 < t) (htop : t ≤ 1 / 2) :
    HasSum (fun n : ℕ => laurentCoeff n * ((t : ℂ) * Complex.I) ^ n)
      (riemannZeta (1 + t * Complex.I) - 1 / (t * Complex.I)) := by
  have hz : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast ht.ne') Complex.I_ne_zero
  simpa only [regularPart, if_neg hz] using regularPart_hasSum ((t : ℂ) * Complex.I)

end LeanLab.ChirreHagen2025.Decomp358e
