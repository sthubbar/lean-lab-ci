/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The redundant nonprincipal condition in the MM14 input is elementary.
Source context: Matomaki and Merikoski, printed page 3, Theorem 1.4.
-/
import LeanLab.Routes.Task59PrimitiveInstance

namespace LeanLab.Routes.Task59

/-- A primitive character at level at least 2 cannot be principal. -/
theorem nonprincipal_of_primitive {q : ℕ} (hq : 2 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  haveI : NeZero q := ⟨by omega⟩
  intro h
  have hc : χ.conductor = 1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mp h
  have hp : χ.conductor = q := hχ
  omega

example : LeanLab.Routes.U1451.chi7 ≠ 1 :=
  nonprincipal_of_primitive (by norm_num) _ primitive_chi7

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.nonprincipal_of_primitive
