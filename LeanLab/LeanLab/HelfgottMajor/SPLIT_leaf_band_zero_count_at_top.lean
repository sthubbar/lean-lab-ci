import LeanLab.HelfgottMajor.SPLIT_zero_count_tall_band_low

/-!
Split of `leaf_band_zero_count_at_top`, the counting content of the first tall band of the
explicit upper count for the nontrivial zeros of a primitive Dirichlet `L`-function.

The statement sits at one height per conductor: the top `2 * π * exp 1 * exp 1 / q` of the band
`2 * π * exp 1 ≤ q * t ≤ 2 * π * exp 1 * exp 1`, where the product `q * t` is the fixed number
`2 * π * exp 1 * exp 1 = 46.4268…` and only the conductor moves, `q ≤ 23`.  Since the product is
constant, the height falls like `1 / q`: it is `46.4268…` at `q = 1`, `23.2134…` at `q = 2` and
`2.0185…` at `q = 23`.  The split below is by conductor, because every estimate of the count is
allowed to depend on which of those heights it is taken at.

NOTE on the third leaf.  `leaf_band_zero_count_at_top_level_one` is FALSE as stated and its
`sorry` is left in place deliberately.  At `q = 1` the character is the principal one of
conductor `1`, it is primitive, its `L`-function is `ζ`, and the height is the whole
`46.4268…`: `ζ` has the eight simple zeros with imaginary parts
`14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 37.5862, 40.9187, 43.3271`, all below `46.4268…`
(the next one is at `48.0051…`), so the multiplicity weighted count at that height is `16`, not
at most `13`.  The band's own budget is `17.7`, which covers `16`; only the constant `13` of this
cut is out of reach.  A repair has to raise that constant to `16`, which is a change of the
sealed statement and not available here.  The other two leaves are the conductor ranges
`2 ≤ q ≤ 11` and `12 ≤ q ≤ 23`, they are not touched by this obstruction, and they are the work
this split hands on.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- LEAF. Conductor one, the whole top of the band.  At `q = 1` the height at the top of the band
is the full product `2 * π * exp 1 * exp 1 = 46.4268…`, so the leaf asks for at most `13`
multiplicity weighted nontrivial zeros of the `L`-function of the principal character of
conductor `1` up to that height.  This is the target with the two range hypotheses of the band
replaced by the single condition `q = 1`; it is FALSE, see the note at the head of the file, and
it is kept as the one leaf that records the constant obstruction. -/
theorem leaf_band_zero_count_at_top_level_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq1 : q = 1) :
    zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) ≤ 13 := by
  sorry

/-- LEAF. Small conductor, `2 ≤ q ≤ 11`.  Here the top of the band is the height
`2 * π * exp 1 * exp 1 / q`, which lies between `46.4268… / 11 = 4.2206…` and
`46.4268… / 2 = 23.2134…`, and the leaf asks for at most `13` multiplicity weighted nontrivial
zeros there.  The conductor range is a proper part of the target's `q ≤ 23`, so this is strictly
easier than the target; what it still needs is the explicit zero data for the primitive
characters of those conductors up to height `23.2134…`. -/
theorem leaf_band_zero_count_at_top_small_level (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) (hq11 : q ≤ 11) :
    zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) ≤ 13 := by
  sorry

/-- LEAF. Large conductor, `12 ≤ q ≤ 23`.  Here the top of the band is the height
`2 * π * exp 1 * exp 1 / q`, which lies between `46.4268… / 23 = 2.0185…` and
`46.4268… / 12 = 3.8689…`, and the leaf asks for at most `13` multiplicity weighted nontrivial
zeros there.  Again a proper part of the target's conductor range, so strictly easier than the
target; at these heights the count is small and what the leaf needs is the low lying zero data of
the primitive characters of conductor `12 ≤ q ≤ 23`, which can only lower it further. -/
theorem leaf_band_zero_count_at_top_large_level (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq12 : 12 ≤ q) (hq23 : q ≤ 23) :
    zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) ≤ 13 := by
  sorry

/-- The sealed statement, assembled from the three conductor ranges: `q = 1`, `2 ≤ q ≤ 11` and
`12 ≤ q ≤ 23`.  Every positive modulus falls into exactly one of them, and each range is one of
the leaves above, so the assembly has no open goal of its own.  The target
`leaf_band_zero_count_at_top` is not used in this file. -/
theorem leaf_band_zero_count_at_top_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≤ 23) :
    zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) ≤ 13 := by
  have hq0 : 0 < q := NeZero.pos q
  rcases lt_or_ge q 2 with h2 | h2
  · exact leaf_band_zero_count_at_top_level_one q χ hχ (by omega)
  rcases lt_or_ge q 12 with h12 | h12
  · exact leaf_band_zero_count_at_top_small_level q χ hχ h2 (by omega)
  · exact leaf_band_zero_count_at_top_large_level q χ hχ h12 hq

end LeanLab.HelfgottMajor.Decomp388a
