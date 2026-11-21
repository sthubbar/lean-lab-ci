import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Complex.Basic

/-!
The conductor fourteen case of the P0014 page 38 zero count is empty.
Every character of level fourteen factors through level seven.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Conductor669

/-- P0014 page 38 display 4.26, the empty conductor fourteen specialization.
The reduction on unit groups has trivial kernel, so no character is primitive. -/
theorem not_primitive_fourteen (χ : DirichletCharacter ℂ 14) : ¬ χ.IsPrimitive := by
  have hi : Function.Injective (ZMod.unitsMap (show 7 ∣ 14 by norm_num)) := by
    decide
  have hf : χ.FactorsThrough 7 := by
    apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap (by norm_num : 7 ∣ 14)).mpr
    intro x hx
    have hx1 : x = 1 := hi (by simpa using hx)
    rw [hx1]
    exact map_one χ.toUnitHom
  have hc : χ.conductor ≤ 7 := Nat.sInf_le hf
  intro hχ
  change χ.conductor = 14 at hχ
  rw [hχ] at hc
  omega

end LeanLab.HelfgottMajor.Conductor669

#print axioms LeanLab.HelfgottMajor.Conductor669.not_primitive_fourteen
