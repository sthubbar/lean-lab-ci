/-
Counterexample to the LEAF `upper_self_scaled_principal_trivial_character` of
SPLIT_upper_self_scaled_principal_distribution. In Mathlib the trivial Dirichlet character
`(1 : DirichletCharacter ℂ q)` is 1 on units of ZMod q and 0 on non units, so at q = 2 and m = 2 it
takes the value 0, not 1. The leaf as stated, for all q and m, is therefore false, and the assembly
`upper_self_scaled_principal_distribution_split` rests on a false leaf. The sealed parent statement
is not refuted here: its sum has the coefficient b1 in front of the character, and b1 may vanish
whenever m shares a factor with a small modulus q. This file adds no definition and edits no
existing file. AI wrote the Lean code.
-/
import LeanLab.BHP1997.SPLIT_upper_self_scaled_principal_distribution

namespace LeanLab.BHP1997.Upper312Route

/-- The trivial character modulo 2 vanishes at 2, a non unit of ZMod 2. -/
theorem trivial_character_two_two_eq_zero :
    (1 : DirichletCharacter ℂ 2) ((2 : ℕ) : ZMod 2) = 0 :=
  MulChar.map_nonunit _ (by decide)

/-- The negation of the universal statement of the LEAF
`upper_self_scaled_principal_trivial_character`: its instance at q = 2, m = 2 fails. PROVED. -/
theorem upper_self_scaled_principal_trivial_character_false :
    ¬ ∀ q m : ℕ, (1 : DirichletCharacter ℂ q) (m : ZMod q) = 1 := by
  intro h
  have h2 := h 2 2
  rw [trivial_character_two_two_eq_zero] at h2
  exact zero_ne_one h2

end LeanLab.BHP1997.Upper312Route
