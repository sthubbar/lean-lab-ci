import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace LeanLab.HardyLittlewood1923.DecompJ1131

open Complex

/-- LEAF. The non-trivial zero of the Riemann zeta function is a complex number.
Textbook argument: Standard analytic number theory. -/
theorem zeta_has_complex_zero : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.im ≠ 0 := by
  sorry

/-- LEAF. The classical existence input to its functional equation argument.
Textbook argument: Landau Handbuch page 489 and the classical theory of zeta zeros. -/
theorem zeta_has_complex_zero_sym : ∃ ρ : ℂ, ρ.im ≠ 0 ∧ riemannZeta ρ = 0 := by
  obtain ⟨ρ, h1, h2⟩ := zeta_has_complex_zero
  exact ⟨ρ, h2, h1⟩

/-- The classical existence input to its functional equation argument.
Textbook argument: Landau Handbuch page 489 and the classical theory of zeta zeros. -/
theorem exists_nonreal_zeta_zero :
    ∃ ρ : ℂ, ρ.im ≠ 0 ∧ riemannZeta ρ = 0 := by
  exact zeta_has_complex_zero_sym

end LeanLab.HardyLittlewood1923.DecompJ1131
