import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
A cut of the nonreal primitive character zero free region of the second proof
paragraph after display 10 into three steps: the arithmetic edge of the region
denominator, the classically known half plane at real part one and above, and the
open strip below one where the analytic content of the region sits. The region
edge is placed on the nonnegative axis in the assembly, which is where the
denominator bound is used.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF. Step one, the arithmetic edge of the region: for a positive modulus the
denominator of the region is at least one, so the edge one minus its reciprocal is
nonnegative and strictly below one. -/
theorem iwaniec_denom_ge_one481 (r : ℕ) (hr : 1 ≤ r) (t : ℝ) :
    (1 : ℝ) ≤ iwaniecDenom481 r t := by
  sorry

/-- LEAF. Step two, the half plane at real part one and above: a nonreal primitive
character does not vanish there, independently of the region denominator. -/
theorem iwaniec_no_zero_half_plane481 (r : ℕ) (hr : 1 ≤ r) (χ : DirichletCharacter ℂ r)
    (hprim : χ.IsPrimitive) (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hs : 1 ≤ s.re) : Lfun481 χ s ≠ 0 := by
  sorry

/-- LEAF. Step three, the open strip below one: a nonreal primitive character does
not vanish strictly between real part zero and one once it lies to the right of the
region edge. This is the analytic content of the region, cut out of the half plane
at one which step two covers. -/
theorem iwaniec_no_zero_open_strip481 (r : ℕ) (hr : 1 ≤ r) (χ : DirichletCharacter ℂ r)
    (hprim : χ.IsPrimitive) (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re) : Lfun481 χ s ≠ 0 := by
  sorry

/-- The region edge sits at nonnegative real part, which is the only place the
denominator bound of step one is needed. -/
private theorem iwaniec_region_pos481 (r : ℕ) (hr : 1 ≤ r) (t : ℝ) {x : ℝ}
    (hx : 1 - 1 / iwaniecDenom481 r t < x) : 0 < x := by
  have h1 : (1 : ℝ) ≤ iwaniecDenom481 r t := iwaniec_denom_ge_one481 r hr t
  have hD : (0 : ℝ) < iwaniecDenom481 r t := lt_of_lt_of_le zero_lt_one h1
  have hq : 1 / iwaniecDenom481 r t ≤ 1 := by
    rw [div_le_iff₀ hD]
    simpa using h1
  linarith

/-- The nonreal primitive character zero free region, from its three steps: the
half plane at one and above, and the strip below one split by the region edge, which
step one keeps on the nonnegative axis. -/
theorem iwaniec_zero_free481_split : IwaniecStatement481 := by
  intro r hr χ hprim hnonreal s hs
  rcases lt_or_ge s.re (1 : ℝ) with hlt | hge
  · exact iwaniec_no_zero_open_strip481 r hr χ hprim hnonreal hlt
      (iwaniec_region_pos481 r hr s.im hs) hs
  · exact iwaniec_no_zero_half_plane481 r hr χ hprim hnonreal hge

end

end LeanLab.LPZ2007
