import LeanLab.HelfgottMajor.SPLIT_leaf_moment_full_mass_plancherel

/-!
Split of the open leaf `leaf_moment_low_mass_le` of
`SPLIT_leaf_moment_full_mass_plancherel.lean`.

The leaf bounds the low band of the discrete Plancherel mass: the zeros of `L χ` in the strip
`0 < re ρ < 1` with `|im ρ| ≤ T`, kept only when `|im ρ| ≤ 1`, each weighted by its
multiplicity and the squared norm of the Gaussian Mellin profile there, are bounded by the
squared `L2` energy `Sec45.nTwo` of the profile, uniformly in the conductor `q` and in `T`.

The split has three steps.  First, the height window `|im ρ| ≤ T` and the indicator `|im ρ| ≤ 1`
are both harmless: the surviving zeros are exactly those with `|im ρ| ≤ 1` and `|im ρ| ≤ T`,
all summands are nonnegative, and converting the index set from `|im ρ| ≤ T` to the fixed band
`|im ρ| ≤ 1` can only add terms (every such zero has `|im ρ| ≤ 1`, and dropping the restriction
`|im ρ| ≤ T` never removes one).  Second and third, the fixed band is cut at the critical line
into the half with `re ρ ≤ 1/2` and the half with `1/2 < re ρ`; each of the two halves is one
leaf, and its bound is the tightened constant `Sec45.nTwo / 2`.

Every step is a separate leaf ending in `sorry`; the assembly `leaf_moment_low_mass_le_split`
below uses only those leaves and no `sorry`.  The two half-strip leaves carry the whole
analytic content: they are one inequality each about the Plancherel mass on a fixed
half-strip of unit height.  Nothing here is proved about the number of zeros in the band.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- LEAF. Window removal.  The height window `|im ρ| ≤ T` and the indicator `|im ρ| ≤ 1` can
both be dropped: every zero that survives them satisfies `|im ρ| ≤ 1`, the summands —
a natural multiplicity times a squared norm — are nonnegative, and re-indexing the surviving
zeros by the fixed band `|im ρ| ≤ 1` only adds the zeros of the band whose height exceeds `T`.
This step estimates nothing about the Mellin norms; it moves the index set and nothing else,
and it is the step that removes the height `T` from the statement. -/
theorem leaf_moment_low_mass_window_restrict (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2) := by
  sorry

/-- LEAF. Lower half of the fixed low band.  On the zeros of `L χ` in the strip with
`|im ρ| ≤ 1` and `re ρ ≤ 1/2`, the multiplicity-weighted squared Mellin mass is at most half
of the squared `L2` energy `Sec45.nTwo` of the profile.  The index set is the low band only,
cut at the critical line from below, and the constant is tightened from `Sec45.nTwo` to
`Sec45.nTwo / 2`; this is one estimate about a fixed half-strip of unit height, and it says
nothing about the half with `re ρ > 1/2`. -/
theorem leaf_moment_low_mass_lower_half (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | ρ.val.re ≤ 1 / 2}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 2 := by
  sorry

/-- LEAF. Upper half of the fixed low band.  On the zeros of `L χ` in the strip with
`|im ρ| ≤ 1` and `1/2 < re ρ`, the multiplicity-weighted squared Mellin mass is at most half
of the squared `L2` energy `Sec45.nTwo` of the profile.  The index set is the low band only,
cut at the critical line from above, and the constant is tightened from `Sec45.nTwo` to
`Sec45.nTwo / 2`; this is one estimate about a fixed half-strip of unit height, and it says
nothing about the half with `re ρ ≤ 1/2`. -/
theorem leaf_moment_low_mass_upper_half (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | 1 / 2 < ρ.val.re}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 2 := by
  sorry

/-- Assembly of the split: drop the height window and the indicator to reach the fixed band
`|im ρ| ≤ 1`, split that band at the critical line into `re ρ ≤ 1/2` and `1/2 < re ρ`, and
bound the two halves by `Sec45.nTwo / 2` each. -/
theorem leaf_moment_low_mass_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo := by
  classical
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} := (leaf_moment_window_finite q χ 1).fintype
  have hsplit :
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 1},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2)
        = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
              |ρ.im| ≤ 1},
            Set.indicator {ρ | ρ.val.re ≤ 1 / 2}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
          + (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
                |ρ.im| ≤ 1},
              Set.indicator {ρ | 1 / 2 < ρ.val.re}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                  ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
    rw [tsum_fintype, tsum_fintype, tsum_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ρ _
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : (ρ : ℂ).re ≤ 1 / 2
    · rw [if_pos h, if_neg (by linarith)]
      ring
    · rw [if_neg h, if_pos (lt_of_not_ge h)]
      ring
  have h1 := leaf_moment_low_mass_window_restrict q χ δ T
  have h2 := leaf_moment_low_mass_lower_half q χ δ T
  have h3 := leaf_moment_low_mass_upper_half q χ δ T
  have h4 :
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 1},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ≤ Sec45.nTwo := by
    rw [hsplit]
    linarith
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
