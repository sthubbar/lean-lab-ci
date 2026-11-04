import Mathlib
import LeanLab.Ramare1995.Section9
import LeanLab.Ramare1995.Decomp1526c

open Finset Real
open scoped Classical

namespace LeanLab.Ramare1995.DecompJ1066
open LeanLab.Ramare1995.Section9
open LeanLab.Ramare1995.Decomp1526c

/-- LEAF p. 653: Ramaré 1995 Proposition 1 p. 653, in the literal interval notation
of equation 2.14 p. 652 and with S2 equal to twice the Euler product,
as on p. 647 and p. 678.
This is the required decomposition leaf for proposition1. -/
theorem proposition1_leaf (X : ℝ) (hX : exp 67 ≤ X) :
    0.478 * X ^ 2 / Real.log X ≤ paper_R X := sorry

/-- CITED. Ramaré 1995 Proposition 1 p. 653, in the literal interval notation
of equation 2.14 p. 652 and with S2 equal to twice the Euler product,
as on p. 647 and p. 678.
This is the assembly theorem for proposition1, identical to the Prop definition. -/
theorem proposition1_assembly : proposition1 :=
  fun X hX => proposition1_leaf X hX

end LeanLab.Ramare1995.DecompJ1066
