/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The missing elementary primitivity instance from the U1451 progress entry.
-/
import LeanLab.Routes.Task59Primitive

namespace LeanLab.Routes.Task59

/-- The nonprincipal quadratic character already exhibited by U1451 is primitive. -/
theorem primitive_chi7 : LeanLab.Routes.U1451.chi7.IsPrimitive :=
  primitive_of_prime_ne_one _ LeanLab.Routes.U1451.vacuity_chi7.2.1

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.primitive_chi7
