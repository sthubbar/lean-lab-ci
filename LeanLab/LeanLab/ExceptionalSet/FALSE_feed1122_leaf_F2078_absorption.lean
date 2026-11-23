import LeanLab.ExceptionalSet.DecompF2078Leaves
import LeanLab.ExceptionalSet.FALSE_leaf_absorption_lemma4

/-!
Burst burst-20261122 feed1122, session S89. The LEAF `U1539.leaf_F2078_absorption` of
`DecompF2078Leaves.lean` is FALSE.

Its statement is word for word the statement of `U1539.leaf_absorption` of `SPLIT_lemma4.lean`,
whose negation `FalseLeafAbsorptionLemma4.not_leaf_absorption` is already kernel checked on
main. Reason: with `H = ⌈log N⌉` the left side holds the term `4N/(⌈log N⌉ + 1)`, about
`4N / log N`, while the right side is `B N exp(-κ (log N)^{3-2γ})`; for `0 < 3 - 2γ < 1` the
factor `exp(κ (log N)^{3-2γ})` outgrows every power of `log N`, so no `κ > 0`, `B ≥ 1` work.
Concrete candidate: `γ = 5/4`, `κ₁ = B₁ = 1`; for given `κ`, `B` any `N` with
`exp(κ (log N)^{1/2}) > B (log N + 2) / 4` fails, for `κ = B = 1` already `N = ⌈e^100⌉`.

This file transfers the negation to the copy in `DecompF2078Leaves`, so the off main record of
omos_tick 20261121T1959Z now has a kernel checked twin on main. The leaf statement is not changed
and this file does not use it. The defect is the lab's choice of the cutoff `H`, not P0082.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.U1539

/-- The negation of `leaf_F2078_absorption`, through the type of the leaf itself. -/
theorem not_leaf_F2078_absorption : ¬ (type_of% @leaf_F2078_absorption) :=
  FalseLeafAbsorptionLemma4.not_leaf_absorption

#print axioms not_leaf_F2078_absorption

end LeanLab.ExceptionalSet.U1539
