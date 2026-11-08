/-
Original pages 157 and 158 equations 4.3 and 4.4.
Keep the complex kernel until after frequency integration.
These identities supply a starting point for a repaired split.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp442a

namespace LeanLab.Linnik1951
open MeasureTheory
open scoped ComplexConjugate

/-- The signed double kernel expands the square of the Mellin integral exactly. -/
theorem mellin_signed_square452 (N : ℕ) (M : ℝ → ℂ) (α : ℝ) :
    ‖mellinU1622 N M α‖ ^ 2 = (1 / (2 * Real.pi)) ^ 2 *
      (∫ t : ℝ, ∫ u : ℝ,
        (mellinKernel442 N α t * M t) *
          conj (mellinKernel442 N α u * M u)).re := by
  let f : ℝ → ℂ := fun t => mellinKernel442 N α t * M t
  have hprod : (∫ t : ℝ, ∫ u : ℝ, f t * conj (f u)) =
      ((‖∫ t : ℝ, f t‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [integral_const_mul]
    rw [integral_conj, integral_mul_const, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hu : mellinU1622 N M α = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, f t := rfl
  change ‖mellinU1622 N M α‖ ^ 2 = (1 / (2 * Real.pi)) ^ 2 *
    (∫ t : ℝ, ∫ u : ℝ, f t * conj (f u)).re
  rw [hu, hprod, Complex.ofReal_re, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)), mul_pow]

/-- The outer square integral equals the integrated signed double kernel.
No absolute value is inserted inside the Mellin integral. -/
theorem mellin_signed_square_integral452 (N : ℕ) (M : ℝ → ℂ) (a b : ℝ) :
    (∫ α in a..b, ‖mellinU1622 N M α‖ ^ 2) =
      (1 / (2 * Real.pi)) ^ 2 * ∫ α in a..b,
        (∫ t : ℝ, ∫ u : ℝ,
          (mellinKernel442 N α t * M t) *
            conj (mellinKernel442 N α u * M u)).re := by
  simp_rw [mellin_signed_square452]
  rw [intervalIntegral.integral_const_mul]

end LeanLab.Linnik1951
