/-
BhowmikGrimmelt2026, P0029, Theorem 3.1 routed assembly. ROUTE BURST burst-20261122, unit
P1122-0009, branch claude/BhowmikGrimmelt2026-wiring1122.

Wiring audit. The main assembly `theorem31_decomposed150` of Decomp150a.lean depends on the two
open route leaves `primitive_psi_zero_expansion508` and `oscillatory_zero_modes508`. It cannot be
rerouted in place: Theorem31Inputs150.lean imports Decomp150a.lean, and Prep1121BGFinish.lean
imports Theorem31Inputs150.lean, so Decomp150a.lean importing the finish file would be an import
cycle. This file is the sealed twin instead: `theorem31_routed1122` has exactly the statement of
`theorem31_decomposed150`, the sealed proposition `Theorem31` of Statements.lean, and its proof is
`theorem31_finish150` applied to the leaf `davenport_integer_half_formula592` of
SPLIT_davenport_integer_formula592.lean. So the only open input under it is that single cited
leaf, Davenport, Multiplicative Number Theory, second edition, chapter 19, pages 117 and 118; the
two route leaves are gone from its dependency cone.

No new definition, no sorry. Pure plumbing, no new mathematics. Binary Goldbach is OPEN: Theorem
3.1 bounds the exceptional set under a zero hypothesis unproved for every Θ below one. AI wrote
the Lean code.
-/
import LeanLab.BhowmikGrimmelt2026.Prep1121BGFinish

namespace LeanLab.BhowmikGrimmelt2026

/-- P0029 Theorem 3.1 page 9, the sealed twin of `theorem31_decomposed150` with the same statement
`Theorem31`. CONDITIONAL ON the single cited leaf `davenport_integer_half_formula592`, Davenport
chapter 19 pages 117 and 118, through `theorem31_finish150`; the route leaves
`primitive_psi_zero_expansion508` and `oscillatory_zero_modes508` are not used. -/
theorem theorem31_routed1122 : Theorem31 :=
  theorem31_finish150 davenport_integer_half_formula592

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.theorem31_routed1122
