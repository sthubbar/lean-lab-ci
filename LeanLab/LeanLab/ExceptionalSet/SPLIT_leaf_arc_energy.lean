import LeanLab.ExceptionalSet.Decomp522a

/-!
Split of `LeanLab.ExceptionalSet.BG2026.Decomp522a.leaf_arc_energy`: the mean square distance
between the square of the exponentially weighted prime generating function and the rectangular arc
model, both cut at the natural square root of `X`.

The target is one eventual inequality for

`∫ t, ‖FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t‖ ^ 2 ∂haarAddCircle`,

namely that it is at most `C · X^(3/2 + 2Θ + ε)` once `X` is large. The cut made here is on the
frequency support of the difference `FX X (X ^ 2) ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X)`. That
difference is square integrable on the circle, since both summands are, so its circle integral is
the sum of the squares of its Fourier coefficients over all integers. Cutting that sum at the
finite set of even frequencies between `0` and `X` gives two pieces:

* `leaf_arc_energy_spectral`, the cut itself: the integral is at most the squared coefficient
  energy on the even frequencies `0 ≤ n ≤ X` plus the squared coefficient energy on the complement
  of that finite frequency set. This is the reduction of route one, the passage from the circle
  integral to spectral energy; it is an inequality at every `X ≥ 1`, not an eventual one.
* `leaf_arc_energy_window`, the first side: the squared coefficient energy on the even frequencies
  `0 ≤ n ≤ X` is eventually at most `C · X^(3/2 + 2Θ + ε)`.
* `leaf_arc_energy_offwindow`, the second side: the squared coefficient energy on the complement of
  that finite frequency set is eventually at most `C · X^(3/2 + 2Θ + ε)`.

The two frequency sets are disjoint and cover every integer coefficient, so their squared energies
add to the full spectral energy, and each side is one estimate about one part of the spectrum. No
one of the three leaves gives the target: the integral needs the cut and both of its sides, and
each side alone is strictly weaker than the target because the other side's energy is dropped.
The assembly `leaf_arc_energy_split` takes `C` to be the sum of the two constants and `X₀` the sum
of the two thresholds plus one, and adds.

Why the leaves are not degenerate. Each leaf carries the target's own numerical hypotheses
`1/2 ≤ Θ`, `Θ < 3/4`, `0 < ε` and `ε < 3/2 - 2 Θ`, so an instance is `Θ = 1/2`, `ε = 1/4`, and
none of the hypotheses can fail to hold together since `3/2 - 2·(1/2) = 1/2 > 0`. The even
frequency set at `X = 4` is `{0, 2, 4}`, which is nonempty, and its complement at `X = 4` contains
the odd frequency `1`, so neither the window nor the off window leaf is an empty claim; the model
`Vfun 4 2 2` is a genuine arc sum with two coprime numerators at `q = 2` and a nonvanishing
coefficient at `0`. At `X = 0` the cutoff `Nat.sqrt 0` is `0` and both sides of the cut are
degenerate, so `leaf_arc_energy_spectral` is stated for `1 ≤ X` only, and the two threshold leaves
carry their own `X₀`, whose honest value is at least `4`. No division by `X`, by the cutoff or by
`Nat.totient` appears in any statement, so the junk values of Lean division play no role; the only
power is `X ^ (3/2 + 2Θ + ε)` at a nonnegative base, and the empty frequency set is handled by the
`Finset` sum being zero and by the indicator sum of the complement being then the full energy.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- LEAF. The cut of the circle integral at the even frequencies up to `X`: for `1 ≤ X`, the square
integral of the difference between the squared generating function cut at `X ^ 2` and the arc model
cut at `Nat.sqrt X` is at most the squared Fourier coefficient energy of that difference on the
even frequencies `0 ≤ n ≤ X` plus its squared coefficient energy on the complement of that finite
frequency set. This is the Parseval step only, at one fixed `X`, with no asymptotic content, no
constant to be found and no hypothesis on `Θ` used beyond carrying it. It drops neither side of the
cut in the way the two threshold leaves do, but asserts no bound on either side. Instance:
`Θ = 1/2`, `ε = 1/4`, `X = 4`, where the window is `{0, 2, 4}` and the complement contains `1`. -/
theorem leaf_arc_energy_spectral (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) (X : ℕ) (hX : 1 ≤ X) :
    (∫ t, ‖FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t‖ ^ 2
        ∂haarAddCircle) ≤
      (∑ n ∈ (range (X + 1)).filter Even,
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
          (n : ℤ)‖ ^ 2) +
      (∑' n : ℤ, if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
        else ‖fourierCoeff
          (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) := by
  sorry

/-- LEAF. The even frequency window `0 ≤ n ≤ X` only: there are `C` and `X₀` with `0 ≤ C` and, for
every `X ≥ X₀`, the squared Fourier coefficient energy of the difference on the even frequencies
`0 ≤ n ≤ X` is at most `C · X^(3/2 + 2Θ + ε)`. This is one side of the spectral cut, stated on
that finite set alone, so it does not imply the target: it says nothing about the coefficients
outside `0 ≤ n ≤ X`. It uses the zero free hypothesis and the numerical hypotheses exactly as the
target does, and it is an eventual inequality, so its constant and threshold are free. Instance:
after the threshold, `Θ = 1/2` and `ε = 1/4`; the summand set at `X = 4` is `{0, 2, 4}`. -/
theorem leaf_arc_energy_window (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑ n ∈ (range (X + 1)).filter Even,
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
          (n : ℤ)‖ ^ 2) ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF. The complement of the even frequency window only: there are `C` and `X₀` with `0 ≤ C` and,
for every `X ≥ X₀`, the squared Fourier coefficient energy of the difference on the integers that
are not an even frequency `0 ≤ n ≤ X` is at most `C · X^(3/2 + 2Θ + ε)`. This is the other side of
the spectral cut, stated on that complement alone, so it does not imply the target: it says nothing
about the coefficients on `0 ≤ n ≤ X`. The complement is infinite and its indicator is written as
zero on the window, so the sum is the energy of the frequencies dropped by the window leaf.
Instance: `Θ = 1/2`, `ε = 1/4`; at `X = 4` the complement contains the odd frequency `1` and every
frequency above `4`, so the claim is not the claim of an empty index set. -/
theorem leaf_arc_energy_offwindow (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
        else ‖fourierCoeff
          (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- Assembly of `leaf_arc_energy` from the cut and its two sides. The spectral leaf bounds the
circle integral by the window energy plus the off window energy at the same `X`; the two threshold
leaves bound those two energies by `C` times the same power of `X`; the constant is their sum and
the threshold the sum of the two thresholds plus one, which puts `X` at least one and at least both
thresholds. Nothing else is used and `sorry` is not used. -/
theorem leaf_arc_energy_split (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∫ t, ‖FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t‖ ^ 2
        ∂haarAddCircle) ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  obtain ⟨Cw, hCw, Xw, hw⟩ := leaf_arc_energy_window Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨Ct, hCt, Xt, ht⟩ := leaf_arc_energy_offwindow Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨Cw + Ct, add_nonneg hCw hCt, Xw + Xt + 1, ?_⟩
  intro X hX
  have hXw : Xw ≤ X := by omega
  have hXt : Xt ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  have hsp := leaf_arc_energy_spectral Θ hΘ1 hΘ2 hZF ε hε hsublinear X hX1
  calc (∫ t, ‖FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t‖ ^ 2
        ∂haarAddCircle)
      ≤ (∑ n ∈ (range (X + 1)).filter Even,
          ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
            (n : ℤ)‖ ^ 2) +
        (∑' n : ℤ, if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
          else ‖fourierCoeff
            (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) := hsp
    _ ≤ Cw * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + Ct * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
        add_le_add (hw X hXw) (ht X hXt)
    _ = (Cw + Ct) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a
