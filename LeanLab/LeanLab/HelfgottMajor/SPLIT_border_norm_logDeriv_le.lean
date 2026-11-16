import LeanLab.HelfgottMajor.SPLIT_strip_count_at_one_le_explicit

/-!
# Split of `border_norm_logDeriv_le` (`HelfgottMajor/SPLIT_strip_count_at_one_le_explicit`)

The target bounds the logarithmic derivative of the `L`-function of a primitive character,
with `s ↦ (s - 1) L(s, χ)` in the principal case, by `0.5 log q + 11.7` on the border of the
box `[-1/4, 5/4] x [-3/2, 3/2]`.  The box is fixed and small in the imaginary direction, so
the pointwise bound is uniform in `im u` and the whole content is the dependence on `q` and
on the real part, that is: on which region of the conductor and of the half plane one is in.

The four leaves below are the four real parts on which a different argument gives the bound.
They are the three standard regions of an `L`-function argument plus the half of the middle
strip nearest the abscissa of absolute convergence:

* `1 ≤ Re u` — the Euler product, where `L'/L` is the absolutely convergent prime sum and no
  power of the conductor is spent at all;
* `1/2 ≤ Re u ≤ 1` — the same prime sum after a partial summation shift, which spends one
  power of `√q` and so exactly `0.5 log q`;
* `0 ≤ Re u ≤ 1/2` — the functional equation taken to the right half plane, which again spends
  one `√q`, together with the gamma factor on the far side of the strip;
* `Re u ≤ 0` — the functional equation with the point reflected to real part at least one,
  where the prime sum converges absolutely, so this is the cheapest region of the four.

Each leaf is an instance of the target on a subregion of the border, hence strictly weaker
than it, and on every one of the four the bound is attained nowhere near its edge: at the
corners of the box the two vertical sides have real part `-1/4` and `5/4` and the two sides
at imaginary part `±3/2` run over the whole real range, so the four regions together cover the
border.  The assembly `border_norm_logDeriv_le_split` is a case split on `Re u` and nothing
else.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitStripCount

open Real MeasureTheory Set Filter
open scoped Topology
open LeanLab.HelfgottArcs Decomp269a Decomp269b
open scoped Interval
open LeanLab.PNTPort.ZetaZeros (tendsto_mul_logDeriv)

/-- LEAF. The region of absolute convergence.  On the part of the border with `1 ≤ Re u` the
logarithmic derivative is the absolutely convergent prime sum
`∑ Λ(n) χ(n) n^{-u}` together with the `q`-dependence of the count of primes below the
conductor, and on the border `|Im u| = 3/2` with `Re u ≤ 5/4` this is at most
`0.5 log q + 11.7`; no power of the conductor is spent here. -/
theorem border_logDeriv_le_of_one_le_re (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      1 ≤ u.re →
      ‖logDeriv (fun s => if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
        else DirichletCharacter.LFunction χ s) u‖ ≤ 0.5 * log q + 11.7 := by
  sorry

/-- LEAF. The upper half of the middle strip.  On the part of the border with
`1/2 ≤ Re u ≤ 1` a partial summation of the prime sum moves the real part to `1` at the price
of one instance of the convexity bound `q^{1/2}`, and the Euler product at real part `1`
supplies the constant, giving `0.5 log q + 11.7`. -/
theorem border_logDeriv_le_of_half_le_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      1/2 ≤ u.re → u.re ≤ 1 →
      ‖logDeriv (fun s => if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
        else DirichletCharacter.LFunction χ s) u‖ ≤ 0.5 * log q + 11.7 := by
  sorry

/-- LEAF. The lower half of the middle strip.  On the part of the border with
`0 ≤ Re u ≤ 1/2` the functional equation expresses `u` through `1 - u`, whose real part is at
least `1/2`, and the two conductor factors together spend exactly one `q^{1/2}`; the gamma
factor is bounded by the explicit form of `Γ'/Γ` on `Re ≥ 3/4`, so the bound is
`0.5 log q + 11.7`. -/
theorem border_logDeriv_le_of_nonneg_le_half (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      0 ≤ u.re → u.re ≤ 1/2 →
      ‖logDeriv (fun s => if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
        else DirichletCharacter.LFunction χ s) u‖ ≤ 0.5 * log q + 11.7 := by
  sorry

/-- LEAF. The left of the strip.  On the part of the border with `Re u ≤ 0` the reflection
`u ↦ 1 - u` lands at real part at least `1`, where the prime sum converges absolutely, and the
two factors of the functional equation cancel in the logarithmic derivative; the remaining
price is one `q^{1/2}` and the gamma factor at real part at least `1`, giving
`0.5 log q + 11.7`. -/
theorem border_logDeriv_le_of_re_le_zero (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      u.re ≤ 0 →
      ‖logDeriv (fun s => if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
        else DirichletCharacter.LFunction χ s) u‖ ≤ 0.5 * log q + 11.7 := by
  sorry

/-! ### The assembly -/

/-- The border bound for the logarithmic derivative, from the four real-part regions above:
the four leaves cover the whole border and nothing else is used. -/
theorem border_norm_logDeriv_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      ‖logDeriv (fun s => if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
        else DirichletCharacter.LFunction χ s) u‖ ≤ 0.5 * log q + 11.7 := by
  intro u hu
  by_cases h0 : u.re ≤ 0
  · exact border_logDeriv_le_of_re_le_zero q χ hχ u hu h0
  · have h0' : 0 < u.re := not_le.mp h0
    by_cases h1 : u.re ≤ 1/2
    · exact border_logDeriv_le_of_nonneg_le_half q χ hχ u hu (le_of_lt h0') h1
    · have h1' : 1/2 < u.re := not_le.mp h1
      by_cases h2 : u.re ≤ 1
      · exact border_logDeriv_le_of_half_le_one q χ hχ u hu (le_of_lt h1') h2
      · exact border_logDeriv_le_of_one_le_re q χ hχ u hu (le_of_lt (not_le.mp h2))

end LeanLab.HelfgottMajor.SplitStripCount
