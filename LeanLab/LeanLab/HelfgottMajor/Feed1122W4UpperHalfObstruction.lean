import LeanLab.HelfgottMajor.SPLIT_leaf_moment_low_mass_upper_half

/-!
Obstruction notes for the two open leaves of `SPLIT_leaf_moment_low_mass_upper_half.lean`,
burst 20261122.

The leaves `leaf_upper_half_low_height_le` and `leaf_upper_half_high_height_le` bound a
weighted zero mass over the zeros of `L χ` with `1 / 2 < re ρ`, uniformly in the modulus `q`
and in the character `χ`, with no hypothesis on `q`.  Under GRH the index set is empty and the
bound is trivial; unconditionally it is not known.  This file proves, sorry free, that each
leaf forces every single zero in its sub-band to carry a weighted mass at most
`Sec45.nTwo / 4`.  For `δ = 0` the profile at a real point `σ` in `(1/2, 1)` is
`2 ^ (σ / 2 - 1) * Γ (σ / 2)`, whose square exceeds `1.5`, while `Sec45.nTwo / 4` is about
`0.2216`.  So the low height leaf at `δ = 0` would rule out every real zero in `(1/2, 1)` of
every Dirichlet `L` function, a Landau Siegel type statement that is open.  The leaves are
therefore not provable with present knowledge and are not split further here.  The book
P0014 uses the zero verification of Platt only for conductors up to an explicit bound, a
hypothesis absent from these leaves.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122W4UpperHalfObstruction
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.DecompJ1153
open LeanLab.HelfgottMajor.SplitGaussian123

/-- One term of a finite nonnegative indicator sum over the unit band is at most the sum. -/
theorem term_le_band_sum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (S : Set {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1})
    (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1}) (hρ : ρ ∈ S) :
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2 ≤
      ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 1},
        Set.indicator S
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := by
  classical
  have hfin := leaf_moment_window_finite q χ 1
  letI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} := hfin.fintype
  rw [tsum_fintype]
  have h := Finset.single_le_sum (s := Finset.univ) (a := ρ)
    (f := Set.indicator S
      (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1} => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2))
    (fun j _ => Set.indicator_nonneg
      (fun x _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) j) (Finset.mem_univ ρ)
  rwa [Set.indicator_of_mem hρ] at h

/-- Consequence of the low height leaf: every zero with `1 / 2 < re ρ < 1` and
`|im ρ| ≤ 1 / 2` carries weighted mass at most `Sec45.nTwo / 4`.  This is the form in which the
leaf is seen to contain an open zero free statement. -/
theorem low_height_leaf_forces_pointwise (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (ρ : ℂ) (h0 : DirichletCharacter.LFunction χ ρ = 0) (hr : 1 / 2 < ρ.re)
    (hr1 : ρ.re < 1) (hi : |ρ.im| ≤ 1 / 2) :
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
        ‖gaussianMellin δ ρ‖ ^ 2 ≤ Sec45.nTwo / 4 :=
  (term_le_band_sum q χ δ {ρ | 1 / 2 < ρ.val.re ∧ |ρ.val.im| ≤ 1 / 2}
    ⟨ρ, h0, by linarith, hr1, by linarith⟩ ⟨hr, hi⟩).trans
    (leaf_upper_half_low_height_le q χ δ T)

/-- Consequence of the high height leaf: every zero with `1 / 2 < re ρ < 1` and
`1 / 2 < |im ρ| ≤ 1` carries weighted mass at most `Sec45.nTwo / 4`. -/
theorem high_height_leaf_forces_pointwise (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (ρ : ℂ) (h0 : DirichletCharacter.LFunction χ ρ = 0) (hr : 1 / 2 < ρ.re)
    (hr1 : ρ.re < 1) (hi : 1 / 2 < |ρ.im|) (hi1 : |ρ.im| ≤ 1) :
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
        ‖gaussianMellin δ ρ‖ ^ 2 ≤ Sec45.nTwo / 4 :=
  (term_le_band_sum q χ δ {ρ | 1 / 2 < ρ.val.re ∧ 1 / 2 < |ρ.val.im|}
    ⟨ρ, h0, by linarith, hr1, hi1⟩ ⟨hr, hi⟩).trans
    (leaf_upper_half_high_height_le q χ δ T)

end LeanLab.HelfgottMajor.Feed1122W4UpperHalfObstruction

