import LeanLab.HelfgottMajor.DecompJ1124

/-!
Split of `explicit_formula_remainder_E` in `DecompJ1124.lean`, page 44, display 4.43.

The single inequality is cut along the two dichotomies that the source argument itself
branches on.

The shift `δ` of the Gaussian.  At `δ = 0` the Mellin transform is that of the plain
Gaussian, every zero weight is an explicit classical value, and the two budget terms
`13.347 * |δ|` and `1 + 6 * |δ|` collapse to `0` and `1`.  For `δ ≠ 0` the mass of the
shifted Gaussian sits at height about `2 * π * |δ|`, which is what the hypothesis
`max (4 * π ^ 2 * |δ|) 100 ≤ T` buys; inside the shifted case the ranges `|δ| ≤ 1` and
`1 < |δ|` are kept apart, because below `1` the shift is absorbed by the standing height
`100` while above `1` the saddle point travels with `|δ|`.

The conductor.  For `q = 1` the main term `fhat etaHeart (-δ) * x` is present and
`log q = 0`, so the right side loses its three logarithmic terms; for `q ≠ 1` that main
term is `0` and the logarithmic budget stays.

The four regimes cover every admissible parameter point, so the assembly at the end of the
file is exactly those case splits together with the specialisations `|0| = 0` and
`log 1 = 0`.  No leaf is the target itself: each one is the target restricted to one
regime, with the right side specialised on that regime.
-/

namespace LeanLab.HelfgottMajor.DecompJ1124
open Real LeanLab.HelfgottArcs Decomp123 Decomp269a

/-- LEAF. The unshifted-frequency step, `δ = 0`.  With no shift the main term is
`fhat etaHeart 0 * x`, the zero weights are those of the plain Gaussian, and the budget
`13.347 * |δ|` vanishes while `1 + 6 * |δ|` is `1`, which is why the right side here carries
neither occurrence of `|δ|`. -/
theorem explicit_formula_remainder_E_zero_frequency (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) (hδ : δ = 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T‖ ≤
      3 * log q + 16.695 + (log q + 6.01) / sqrt x := by
  sorry

/-- LEAF. The principal-conductor step, `q = 1` with a genuine shift.  Here the main term
is the non-zero `fhat etaHeart (-δ) * x` and `log q = log 1 = 0`, so the whole logarithmic
budget of the target collapses to the single constant `6.01`; what remains is the shifted
Gaussian against the trivial character. -/
theorem explicit_formula_remainder_E_principal_conductor (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) (hq : q = 1) (hδ : δ ≠ 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T‖ ≤
      13.347 * |δ| + 16.695 + 6.01 * (1 + 6 * |δ|) / sqrt x := by
  sorry

/-- LEAF. The small-shift step for a non-principal conductor.  The conductor is at least
`2`, so the principal main term of the target is `0` and is dropped from the left side,
while the logarithmic budget `3 * log q + (log q + 6.01) / sqrt x` stays.  On `|δ| ≤ 1` the
shift of the Gaussian is smaller than the standing height `100`, so the height hypothesis
`max (4 * π ^ 2 * |δ|) 100 ≤ T` is at its `100` branch and the zero sums run over every zero
below that height. -/
theorem explicit_formula_remainder_E_small_shift (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) (hq : q ≠ 1) (hδ : |δ| ≤ 1)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖Schi etaHeart χ δ x + lowZeros χ δ x T + highZeros χ δ x T‖ ≤
      3 * log q + 13.347 * |δ| + 16.695 + (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  sorry

/-- LEAF. The large-shift step for a non-principal conductor.  As in the small-shift step
the principal main term is `0` and is dropped; here `1 < |δ|`, so `4 * π ^ 2 * |δ|` is the
active branch of the height hypothesis `max (4 * π ^ 2 * |δ|) 100 ≤ T` and the saddle point
of the shifted Gaussian, at height about `2 * π * |δ|`, has to be tracked explicitly
against the zero sum up to `T`. -/
theorem explicit_formula_remainder_E_large_shift (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) (hq : q ≠ 1) (hδ : 1 < |δ|)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖Schi etaHeart χ δ x + lowZeros χ δ x T + highZeros χ δ x T‖ ≤
      3 * log q + 13.347 * |δ| + 16.695 + (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  sorry

/-- The target `explicit_formula_remainder_E`, character for character, assembled from the
four regime leaves.  The only work here is the case split and the specialisations
`|0| = 0`, `log 1 = 0` and `Schi - 0 = Schi`. -/
theorem explicit_formula_remainder_E_split (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T‖ ≤
      (3 * log q + 13.347 * |δ| + 16.695) +
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  by_cases hq : q = 1
  · by_cases hδ : δ = 0
    · subst hδ
      have h := explicit_formula_remainder_E_zero_frequency x hx q χ hχ 0 T rfl hT hzeros
      simpa using h
    · have h := explicit_formula_remainder_E_principal_conductor x hx q χ hχ δ T hq hδ hT hzeros
      simpa [hq] using h
  · by_cases hδ : |δ| ≤ 1
    · have h := explicit_formula_remainder_E_small_shift x hx q χ hχ δ T hq hδ hT hzeros
      simpa [hq] using h
    · have h := explicit_formula_remainder_E_large_shift x hx q χ hχ δ T hq (not_le.mp hδ) hT hzeros
      simpa [hq] using h

#print axioms explicit_formula_remainder_E_split

end LeanLab.HelfgottMajor.DecompJ1124
