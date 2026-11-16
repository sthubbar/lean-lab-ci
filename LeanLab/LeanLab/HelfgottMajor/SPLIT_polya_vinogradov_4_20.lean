import LeanLab.HelfgottMajor.PolyaVinogradov123

/-!
Split of the explicit Polya-Vinogradov inequality for a primitive character modulo `q > 1`
(Helfgott, Major arcs, display 4.20), which is stated in the parent module without proof.

The display has two branches, for the two parities of the character, and the two branches come
from two different Fourier expansions of the sawtooth kernel: the even one has kernel coefficients
`2/(pi^2 k^2)`-sized, the odd one `1/(2 pi k)`-sized, which is why the constants differ. Each branch
is therefore stated here as its own leaf, and the assembly is the parity split.

No definition is introduced: the partial sum of `chi` is written out, and the constant
`M(q)` of the display is written as the supremum of its norm over the length.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real

/-- LEAF: the even branch of the display. If the primitive character satisfies `chi (-1) = 1`, then
the partial sums of `chi` are bounded by the three-term expression with the `2/pi^2` and `4/pi^2`
constants, obtained by summing the `h`-th Fourier coefficient of the even sawtooth kernel over a
harmonic range `h <= H` and then optimizing in `H`. This is one branch, not the whole display: it
says nothing about odd characters. -/
theorem leaf_even_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_even : χ (-1) = 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q := by
  sorry

/-- LEAF: the odd branch of the display. If the primitive character satisfies `chi (-1) ≠ 1`, then
the partial sums of `chi` are bounded by the three-term expression with the `1/(2*pi)` and `1/pi`
constants, obtained by summing the Fourier coefficients of the odd sawtooth kernel over a harmonic
range `h <= H` and then optimizing in `H`. This is one branch, not the whole display: it says
nothing about even characters. -/
theorem leaf_odd_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  sorry

/-- The display, assembled from its two parity branches: split on the value of `chi (-1)` and hand
each branch to the corresponding leaf. -/
theorem polya_vinogradov_4_20_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      if χ (-1) = 1 then
        2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q
      else
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  split_ifs with h
  · exact leaf_even_case χ hχ hq h
  · exact leaf_odd_case χ hχ hq h

end LeanLab.HelfgottMajor.PolyaVinogradov123
