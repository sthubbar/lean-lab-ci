/-
BhowmikGrimmelt2026, P0029, Theorem 3.1 with the Davenport chapter 19 input replaced by the
PNTPort port. ROUTE BURST burst-20261122, session S65, branch
claude/BhowmikGrimmelt2026-integrate1122, stacked on claude/PNTPort-ExplicitPsi1-assembly1122.

`davenport_integer_half_formula592_ported` has exactly the statement of the cited leaf
`davenport_integer_half_formula592` of SPLIT_davenport_integer_formula592.lean, Davenport,
Multiplicative Number Theory, second edition, chapter 19 pages 115 to 118, and is proved from
`PNTPort.ExplicitPsi1.CharHalfAssembly1122.davenport_half_formula_assembled`; `mult χ ρ` is by
definition `analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ`. `theorem31_ported1122` then
has the statement `Theorem31` of `theorem31_decomposed150`, through `theorem31_finish150`.
Both are CONDITIONAL ON the one port LEAF `contour_good_height_leaf`, Davenport ch. 19 pp. 116
and 117, the contour shift at a good height, instead of the whole cited formula.

No new definition, no sorry. Binary Goldbach is OPEN: Theorem 3.1 bounds the exceptional set
under a zero hypothesis unproved for every Θ below one. AI wrote the Lean code.
-/
import LeanLab.BhowmikGrimmelt2026.Prep1121BGFinish
import LeanLab.PNTPort.ExplicitPsi1.CharHalfAssembly1122

namespace LeanLab.BhowmikGrimmelt2026

/-- Davenport, Multiplicative Number Theory, second edition, ch. 19 pp. 115 to 118, the half
weighted integer formula, exactly the statement of `davenport_integer_half_formula592`.
CONDITIONAL ON the one port LEAF `contour_good_height_leaf` of
`PNTPort.ExplicitPsi1.CharHalfAssembly1122`. -/
theorem davenport_integer_half_formula592_ported :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n) :=
  PNTPort.ExplicitPsi1.CharHalfAssembly1122.davenport_half_formula_assembled

/-- P0029 Theorem 3.1 page 9, the statement `Theorem31` of `theorem31_decomposed150`, through
`theorem31_finish150`. CONDITIONAL ON the one port LEAF `contour_good_height_leaf`, Davenport
ch. 19 pp. 116 and 117, in place of the whole cited formula `davenport_integer_half_formula592`. -/
theorem theorem31_ported1122 : Theorem31 :=
  theorem31_finish150 davenport_integer_half_formula592_ported

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.davenport_integer_half_formula592_ported
#print axioms LeanLab.BhowmikGrimmelt2026.theorem31_ported1122
