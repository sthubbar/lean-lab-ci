import LeanLab.HelfgottMajor.SPLIT_leaf_high_mass_bounded_height_le

/-!
Burst-20261122 S94, falsification record for the two open leaves of
`SPLIT_leaf_high_mass_bounded_height_le.lean`, namely `leaf_high_mass_absolute_box_le` and
`leaf_high_mass_delta_box_le`.

Both leaves are reported FALSE on numerical evidence, so they are not split.  This file holds only
the two proved bookkeeping facts that the counterexample uses:

* `nLog_div_four_lt`: the right side `Sec45.nLog / 4` of both leaves is below `0.4869`;
* `LFunction_modOne_eq_riemannZeta`: for the modulus `q = 1` the lab's `L χ` is `riemannZeta`,
  so the zeros counted in the leaves at `q = 1` are exactly the nontrivial zeros of zeta.

The numerics are in `notes/burst-20261122/HelfgottMajor-feed1122-SPLIT_leaf_high_mass_bounded_height_le.md`:
with `q = 1`, `T = 100`, `δ = 12`, the 29 zeta zero pairs with `14 < |γ| ≤ 100` give the
absolute box sum `≈ 1.2466 > 0.4869`, and for `δ = 20` the `δ` selected box sum is computed there.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- Bookkeeping for the falsification: the right side of both box leaves is below `0.4869`. -/
theorem nLog_div_four_lt : Sec45.nLog / 4 < 0.4869 := by
  have h := Sec45.nLog_le
  linarith

/-- Bridge for the falsification: at modulus one the Dirichlet `L` function of the unique
character is the Riemann zeta function, Mathlib `DirichletCharacter.LFunction_modOne_eq`. -/
theorem LFunction_modOne_eq_riemannZeta (χ : DirichletCharacter ℂ 1) :
    DirichletCharacter.LFunction χ = riemannZeta :=
  DirichletCharacter.LFunction_modOne_eq

end LeanLab.HelfgottMajor.DecompJ1153
