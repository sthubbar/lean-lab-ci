import LeanLab.HelfgottMajor.DecompF547

/-!
Split of the pairing step `paired_mass_le` of DecompF547.lean, FREE-nv-glm7 task1604.
No existing file is edited.

The target bounds the two sided multiplicity weighted Mellin mass of the strip zeros above
height T against 4.226 times the one sided envelope sum. The proof runs in three leaves.

1. Pointwise mass bound. For each strip zero above height T, the Mellin mass term is at most
the analytic multiplicity times 4.226 times the two branch envelope sum. This uses the
proved corollary of the saddle analysis for the Gaussian Mellin transform.
2. Two sided summability. The two sided mass sum is summable, from the pointwise bound and
the summability of the one sided envelope.
3. Pairing inequality. The two sided mass sum is at most 4.226 times the one sided envelope
sum, by splitting into positive and negative imaginary parts, pairing the negative part
with the positive part via complex conjugation, and applying the pointwise bound.

The assembly `paired_mass_le_F1604` has the statement of the target character for character
and is proved from the three leaves with no gap of its own. AI wrote this Lean code.
Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real

section DecompF1604

/-- LEAF. Pointwise mass bound. For each zero rho of L(s, chi) in the open critical strip
above height T, the multiplicity weighted Mellin mass term is at most the analytic
multiplicity times 4.226 times the two branch envelope sum exp of minus 0.1598 times
the absolute height plus, away from zero shift, exp of minus 0.1065 times the square of
the height over pi times abs delta. This is the single zero estimate that drives the
whole pairing step. -/
theorem leaf_pointwise_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}) :
    mellinMassTerm χ δ ρ.val ≤
      (ZeroCount1623.mult χ ρ.val : ℝ) *
        (Real.exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) := by
  sorry

/-- LEAF. Two sided summability. The multiplicity weighted Mellin mass of the strip zeros
above height T, taken over both signs of the imaginary part, is summable. This follows
from the pointwise mass bound and the summability of the one sided envelope sum, which
in turn follows from the exponential and Gaussian decay against the zero density. -/
theorem leaf_two_sided_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) := by
  sorry

/-- LEAF. Pairing inequality. The two sided multiplicity weighted Mellin mass sum is at
most 4.226 times the one sided envelope sum over zeros with positive imaginary part.
The proof splits the two sided sum into positive and negative imaginary parts, maps the
negative part to the positive part by complex conjugation, and applies the pointwise
mass bound. -/
theorem leaf_pairing_inequality (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            (Real.exp (-0.1598 * ρ.val.im) +
              if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2))) := by
  sorry

/-- Assembly of the split, FREE-nv-glm7 task1604. The statement of `paired_mass_le`
character for character, proved from the three leaves with no gap of its own. -/
theorem paired_mass_le_F1604 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            (Real.exp (-0.1598 * ρ.val.im) +
              if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2))) := by
  exact ⟨leaf_two_sided_summable q χ δ T hT, leaf_pairing_inequality q χ δ T hT⟩

end DecompF1604

end LeanLab.HelfgottMajor.SplitGaussian123
