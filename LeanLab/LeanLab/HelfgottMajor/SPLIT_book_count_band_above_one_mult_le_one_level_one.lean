import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le

/-!
# Split of `book_count_band_above_one_mult_le_one_level_one`

At conductor `1` the character is trivial and `L(·, χ)` is the Riemann zeta function, by
Mathlib `DirichletCharacter.LFunction_modOne_eq`; this reduction is proved below. The window
`(1, 2πe]`, with `2πe < 17.08`, is then cut at height `14`:

* LEAF: `ζ` has no zero in the open strip with ordinate in `(1, 14]`, the classical fact that
  the first zero of `ζ` above the real axis is at height `14.1347…`;
* LEAF: on `(14, 2πe]` the zeros of `ζ` in the strip are simple, the zero
  `1/2 + 14.1347… i` being the only one there.

Numerically, burst S97 with mpmath: the only zero of `ζ` with ordinate in `(1, 17.08]` is at
`14.134725`, and it is simple; the next one is at `21.022`. AI wrote this Lean code. Binary
Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF: the first ordinate of the nontrivial zeros of `ζ` exceeds `14`, restricted to the
window `(1, 14]` of the band at conductor `1`: no zero of `ζ` in the open strip has ordinate in
`(1, 14]`. Class HARD: a certified zero free rectangle for `ζ`, by Backlund style argument
principle or a Turing method computation. -/
theorem one1_zeta_zero_free_below_fourteen (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him1 : 1 < ρ.im) : 14 < ρ.im := by
  sorry

/-- LEAF: the zeros of `ζ` in the open strip with ordinate in `(14, 2πe]` are simple, the window
holding only `1/2 + 14.1347… i`, a simple zero. Class HARD: a certified simplicity check, for
instance a Turing method count matched against sign changes of Hardy's `Z` function. -/
theorem one1_zeta_simple_fourteen_band (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 14 < ρ.im) (him' : ρ.im ≤ 2 * Real.pi * Real.exp 1) :
    analyticOrderNatAt riemannZeta ρ ≤ 1 := by
  sorry

/-- Assembly of `book_count_band_above_one_mult_le_one_level_one`: at conductor `1` the `L`-function is `ζ`; every element of the window
has ordinate above `14` by the zero free leaf, and is then simple by the simplicity leaf. -/
theorem book_count_band_above_one_mult_le_one_level_one_of_leaves (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 1) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  subst hq
  have hL : DirichletCharacter.LFunction χ = riemannZeta := DirichletCharacter.LFunction_modOne_eq
  intro ρ hρ
  have hp := Finset.mem_filter.mp hρ
  have hz := (stripZeros_finite χ (2 * Real.pi * Real.exp 1)).mem_toFinset.mp hp.1
  have hz0 : riemannZeta ρ = 0 := by rw [← hL]; exact hz.1
  have h14 := one1_zeta_zero_free_below_fourteen ρ hz0 hz.2.1 hz.2.2.1 hp.2.2
  have hs := one1_zeta_simple_fourteen_band ρ hz0 hz.2.1 hz.2.2.1 h14
    ((le_abs_self ρ.im).trans hz.2.2.2)
  have hm : mult χ ρ ≤ 1 := by
    unfold mult; rw [hL]; exact hs
  exact_mod_cast hm

end LeanLab.HelfgottMajor.ZeroCount1623
