/-
Kumchev and Liu 2007, P0088. ROUTE BURST S98 burst-20261122 deepen of
`leaf_moebius_rough` of SPLIT_lemma34_second_sum_dyadic_b.lean: proved outright,
from Mathlib's Moebius inversion `moebius_mul_coe_zeta`, by passing to the
squarefree kernel g of the z smooth part of k.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_lemma34_second_sum_dyadic_b

namespace LeanLab.KumchevLiu2007.Eq33RouteD.SplitB

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- The split statement is the leaf statement. -/
example : type_of% @leaf_moebius_rough := leaf_moebius_rough_split

end LeanLab.KumchevLiu2007.Eq33RouteD.SplitB
