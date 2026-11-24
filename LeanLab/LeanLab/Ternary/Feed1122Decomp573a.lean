/-
Helfgott https://arxiv.org/abs/1312.7748v2 pages 50, 51 and 63.
Feed glue: the Task573 remainder moment is the Task580 remainder moment.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp573a
import LeanLab.Ternary.Decomp580c

namespace LeanLab.Ternary.Task573.Feed1122
open MeasureTheory

/-- The Task573 and Task580 minor domains are the same set.
Helfgott page 10 equation 3.5 at delta zero eight and r zero 150000. -/
theorem minorDomain_eq (x : ℝ) : minorDomain x = Task580.minorDomain x := rfl

/-- The Task573 and Task580 remainder series agree.
Helfgott page 50 proof of Theorem 6.3, definition of S two eta plus. -/
theorem remainderSeries_eq (x α : ℝ) :
    remainderSeries x α = Task580.remainderSeries x α := rfl

/-- The Task573 and Task580 eta star norm weights agree.
Helfgott page 50 proof of Theorem 6.3 and page 60 equation 7.19. -/
theorem starNorm_eq (x α : ℝ) : starNorm x α = Task580.starNorm x α := rfl

/-- The original remainder_moment_upper statement, proved from the Task580
remainder assembly. Helfgott pages 50 and 51 and page 63 equation 7.27.
CONDITIONAL ON the existing leaf Task580.star_mass_error, Helfgott page 59
equation 7.16; the coefficient square estimates are proved in Decomp580c. -/
theorem remainder_moment_upper_of_leaves (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∫ α in minorDomain x, starNorm x α * ‖remainderSeries x α‖ ^ 2) ≤
      1.0532e-11 * (x ^ 2 / LeanLab.Helfgott2013.κ) :=
  Task580.remainder_moment_upper x hx

end LeanLab.Ternary.Task573.Feed1122
