import LeanLab.ExceptionalSet.Decomp371d

/-!
Split of the sealed statement `leaf_poisson` of `LeanLab.ExceptionalSet.Decomp371d`
into four strictly smaller steps, plus an assembly `leaf_poisson_split` whose statement is
the sealed statement and whose proof uses only the four leaves.

The steps are the usual two halves of a Poisson summation argument:
* the summation identity itself, over the integer shifts of the modulated kernel;
* the vanishing of the Fourier transform of `K` at the two unit frequencies, which is where
  the continuity of `K` enters, since the support hypothesis only covers `|α| > 1`;
* the index bookkeeping that singles out the two integer shifts whose frequency falls in the
  unit interval;
* the collapse of the resulting series to those two terms.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371d

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- LEAF. Poisson summation step: the sum of the modulated integer shifts of `K` equals the
sum of the Fourier transform of `K` at the shifted frequencies `v + m`, each carrying the
phase `eC (α * m)`. This is the analytic half of the proof, and it is where the
integrability of `K` is used. -/
theorem leaf_poisson_summation (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      ∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) := by
  sorry

/-- LEAF. Endpoint step: the Fourier transform of `K` vanishes on the closed unit pair of
frequencies `±1` as well. The support hypothesis gives this only for `1 < |α|`; the values at
`|α| = 1` follow from continuity of `α ↦ ftR K α`, which integrability of `K` supplies. -/
theorem leaf_poisson_endpoint (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    ∀ ξ : ℝ, 1 ≤ |ξ| → ftR K ξ = 0 := by
  sorry

/-- LEAF. Index step: every integer shift `m` other than `-⌊v⌋` and `-(⌊v⌋ + 1)` puts the
frequency `v + m` at distance at least `1` from the origin. This is the only point where the
floor and fractional part of `v` are used. -/
theorem leaf_poisson_index (v : ℝ) :
    ∀ m : ℤ, m ≠ -⌊v⌋ → m ≠ -(⌊v⌋ + 1) → 1 ≤ |v + (m : ℝ)| := by
  sorry

/-- LEAF. Collapse step: by the endpoint and index steps, all but the shifts `-⌊v⌋` and
`-(⌊v⌋ + 1)` drop out of the Fourier series, and the two survivors are the terms of the
right-hand side, since `v + (-⌊v⌋) = Int.fract v` and `v + (-(⌊v⌋ + 1)) = Int.fract v - 1`. -/
theorem leaf_poisson_collapse (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  sorry

/-- Assembly: the sealed statement, from the summation leaf and the collapse leaf. -/
theorem leaf_poisson_split (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  rw [leaf_poisson_summation K hK hcont hsupp v α,
    leaf_poisson_collapse K hK hcont hsupp v α]

end LeanLab.ExceptionalSet.Decomp371d
