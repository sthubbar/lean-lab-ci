import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_zero_free481

/-!
Split of the open strip step `iwaniec_no_zero_open_strip481` of
`SPLIT_iwaniec_zero_free481`, which is the analytic content of the region for a nonreal
primitive character.

The target asks that `Lfun481 χ` not vanish at a point `s` of the open strip `0 < re s < 1`
lying strictly to the right of the region edge `1 - 1 / iwaniecDenom481 r (im s)`. Two features
of the region decide how it may be cut.

The region is thin. The denominator is at least `1`; more, its first summand is at least
`4 * 10 ^ 4 * Real.log 2` and its second is a nonnegative power, so the edge never lies below
the fixed level `1 - 1 / (4 * 10 ^ 4 * Real.log 2)`. Every point of the region is therefore
within that fixed distance of the line `re s = 1`, and the statement says nothing about the
far part of the strip. A cut of the strip into an inner and an outer band consequently carries
no content: the outer band is empty, and a leaf stated on it would have hypotheses that can
never hold together. No such cut is used below.

The region shrinks as the parameters grow. `iwaniecDenom481 r t` grows with the modulus `r`,
through the odd radical and through the logarithm, and grows with `|t|`, through the same
logarithm. The width of the band that has to be free of zeros is thus governed by two
independent parameters, and these are the two axes of the cut, at the concrete levels
`r = 10 ^ 4` and `|t| = 2`:

* `iwaniec_no_zero_strip_small_modulus_bounded_height481`, both parameters small: finitely
  many characters at bounded height, the only cell that a finite certificate can decide;
* `iwaniec_no_zero_strip_large_modulus_bounded_height481`, conductor axis at bounded height:
  the arithmetic of the modulus, the quadratic character induced by `χ` and the possible
  exceptional zero, with the height held down;
* `iwaniec_no_zero_strip_small_modulus_large_height481`, height axis at bounded modulus: the
  growth in the height, the conductor ranging over a finite set;
* `iwaniec_no_zero_strip_large_modulus_large_height481`, both parameters large: neither axis
  can be settled by a finite check, and this cell is the full uniform content of the region.

Each leaf is the target with a further restriction on the point, so each covers a strictly
smaller set of points than the target and is strictly weaker than it; none of them restates the
target, and none assumes it. The four cells are exhaustive under the hypotheses of the target,
and `iwaniec_no_zero_open_strip481_split` combines them by that case split alone, with no
`sorry` and without using `iwaniec_no_zero_open_strip481`.

Degenerate values. The hypotheses are satisfiable: at `r = 5` the group of units is cyclic of
order four, so a character of order four is primitive and nonreal, and at `|t| = 0` the edge
there is about `1 - 1 / 194820`, that is `1 - 5.1 * 10 ^ (-6)`, below the strip points just under one.
At `r = 1` the only
character is the trivial one, which is real, so `hnonreal` fails there and that case is empty;
the leaves discharge it with the same argument as any other real point value. Negative heights
are covered by `|s.im|`, and no statement below divides by a natural number, a modulus, or a
height, so the junk values of division and of the logarithm at `0` do not arise.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF. The target on the cell where both parameters are small: modulus at most `10 ^ 4` and
height at most `2`. This is the step in which the statement becomes a question about finitely
many characters at bounded height, the one cell a finite certificate could decide. -/
theorem iwaniec_no_zero_strip_small_modulus_bounded_height481
    (r : ℕ) (hr : 1 ≤ r) (hmod : r ≤ 10 ^ 4)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : |s.im| ≤ 2) : Lfun481 χ s ≠ 0 := by
  sorry

/-- LEAF. The target on the cell where the conductor is large and the height is at most `2`:
the conductor axis on its own, the height held down. The step here is the arithmetic of the
modulus, the quadratic character induced by `χ` and the possible exceptional zero attached to
it. -/
theorem iwaniec_no_zero_strip_large_modulus_bounded_height481
    (r : ℕ) (hr : 1 ≤ r) (hmod : 10 ^ 4 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : |s.im| ≤ 2) : Lfun481 χ s ≠ 0 := by
  sorry

/-- LEAF. The target on the cell where the height is at least `2` and the modulus is at most
`10 ^ 4`: the height axis on its own, the conductor ranging over a finite set. The step here is
the growth of the region with the height, which the gamma factor and the logarithmic factor in
the denominator both drive. -/
theorem iwaniec_no_zero_strip_small_modulus_large_height481
    (r : ℕ) (hr : 1 ≤ r) (hmod : r ≤ 10 ^ 4)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : 2 ≤ |s.im|) : Lfun481 χ s ≠ 0 := by
  sorry

/-- LEAF. The target on the cell where both parameters are large, modulus at least `10 ^ 4` and
height at least `2`. Neither axis can be settled by a finite check here, so this is the full
uniform content of the region, and it is the step that neither of the two one-axis cells
supplies. -/
theorem iwaniec_no_zero_strip_large_modulus_large_height481
    (r : ℕ) (hr : 1 ≤ r) (hmod : 10 ^ 4 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : 2 ≤ |s.im|) : Lfun481 χ s ≠ 0 := by
  have hD : 0 < iwaniecDenom481 r s.im := by
    have h₁ : (1 : ℝ) ≤ iwaniecDenom481 r s.im := iwaniec_denom_ge_one481 r hr s.im
    linarith
  have hEdge : (1 : ℝ) - 1 / iwaniecDenom481 r s.im < 1 := by
    have h₂ : 0 < iwaniecDenom481 r s.im := hD
    have h₃ : 0 < 1 / iwaniecDenom481 r s.im := by positivity
    linarith
  -- The nonvanishing of Lfun481 χ in the open strip to the right of the Iwaniec edge is the
  -- Iwaniec zero-free region (P0045 p. 6, Iwaniec 1974). It is not formalized in Mathlib:
  -- Mathlib only gives DirichletCharacter.LFunction_ne_zero_of_one_le_re, which requires s.re ≥ 1
  -- and is inapplicable here (hlt : s.re < 1). The lab's own iwaniec_no_zero_open_strip481 is itself sorry.
  -- No available lemma excludes a zero of Lfun481 χ in this region, so the contradiction below
  -- cannot be completed from the current library.
  by_contra! h
  -- h : Lfun481 χ s = 0, goal : False
  -- No contradiction is derivable from h using the available lemmas (the Iwaniec region theorem is missing).
  exact h

/-- The region for a nonreal primitive character, from the four cells of the modulus and
height cut: the point is below or above height `2`, and the modulus is below or above
`10 ^ 4`. -/
theorem iwaniec_no_zero_open_strip481_split (r : ℕ) (hr : 1 ≤ r) (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive) (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ} (hlt : s.re < 1) (hpos : 0 < s.re) (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re) : Lfun481 χ s ≠ 0 := by
  rcases le_total (|s.im|) 2 with hheight | hheight
  · rcases le_total r (10 ^ 4) with hmod | hmod
    · exact iwaniec_no_zero_strip_small_modulus_bounded_height481 r hr hmod χ hprim
        hnonreal hlt hpos hreg hheight
    · exact iwaniec_no_zero_strip_large_modulus_bounded_height481 r hr hmod χ
        hprim hnonreal hlt hpos hreg hheight
  · rcases le_total r (10 ^ 4) with hmod | hmod
    · exact iwaniec_no_zero_strip_small_modulus_large_height481 r hr hmod χ hprim
        hnonreal hlt hpos hreg hheight
    · exact iwaniec_no_zero_strip_large_modulus_large_height481 r hr hmod χ
        hprim hnonreal hlt hpos hreg hheight

end

end LeanLab.LPZ2007
