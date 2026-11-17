import LeanLab.HelfgottMajor.SPLIT_leaf_moment_low_mass_le

/-!
Split of the open leaf `leaf_moment_low_mass_upper_half` of
`SPLIT_leaf_moment_low_mass_le.lean`.

The target bounds the multiplicity-weighted squared Mellin mass carried by the zeros of
`L χ` in the half-strip `0 < re ρ < 1`, `1 / 2 < re ρ`, `|im ρ| ≤ 1` by half of the
squared `L2` energy `Sec45.nTwo` of the Gaussian profile.

The split cuts that half-strip by height.  Inside the band `|im ρ| ≤ 1` the condition
`1 / 2 < re ρ` is the disjunction of `1 / 2 < re ρ` with `|im ρ| ≤ 1 / 2` and of
`1 / 2 < re ρ` with `1 / 2 < |im ρ| ≤ 1`, so the mass over the half-strip is the sum of two
sub-band masses; that is one identity leaf.  Each sub-band is then one estimate, carrying
half of the constant of the target: `Sec45.nTwo / 4` for the low sub-band and
`Sec45.nTwo / 4` for the high sub-band, whose sum restores the constant
`Sec45.nTwo / 2`.  The same convention of halving the constant across a cut is what the
imported file applies at the critical line.

Each step is a separate leaf ending in `sorry`; the assembly
`leaf_moment_low_mass_upper_half_split` below uses only those leaves and no `sorry`.  The
two quarter-band leaves carry the whole analytic content; nothing here is proved about the
number of zeros in the band.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- LEAF. Height cut of the upper half of the low band.  On the band `|im ρ| ≤ 1` the
condition `1 / 2 < re ρ` splits into the disjunction of `1 / 2 < re ρ` with
`|im ρ| ≤ 1 / 2` and of `1 / 2 < re ρ` with `1 / 2 < |im ρ|`; the summand is a
multiplicity times a squared norm, so the mass over the half-strip is the sum of the two
sub-band masses.  This step only rearranges the index set: it estimates nothing, assumes
nothing about the Mellin norms, and it is what turns the half-strip of the target into two
sub-bands. -/
theorem leaf_upper_half_mass_height_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | 1 / 2 < ρ.val.re}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) =
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | 1 / 2 < ρ.val.re ∧ |ρ.val.im| ≤ 1 / 2}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) +
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | 1 / 2 < ρ.val.re ∧ 1 / 2 < |ρ.val.im|}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
  classical
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} := (leaf_moment_window_finite q χ 1).fintype
  rw [tsum_fintype, tsum_fintype, tsum_fintype, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro ρ _
  by_cases hr : (1 : ℝ) / 2 < (ρ : ℂ).re
  · rw [Set.indicator_of_mem (show ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1} | 1 / 2 < ρ.val.re} from hr)]
    by_cases hi : |(ρ : ℂ).im| ≤ 1 / 2
    · rw [Set.indicator_of_mem (show ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1} | 1 / 2 < ρ.val.re ∧ |ρ.val.im| ≤ 1 / 2}
          from ⟨hr, hi⟩),
        Set.indicator_of_notMem (show ρ ∉ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1} | 1 / 2 < ρ.val.re ∧ 1 / 2 < |ρ.val.im|}
          from fun h => absurd h.2 (not_lt.mpr hi))]
      ring
    · rw [Set.indicator_of_notMem (show ρ ∉ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1} | 1 / 2 < ρ.val.re ∧ |ρ.val.im| ≤ 1 / 2}
          from fun h => hi h.2),
        Set.indicator_of_mem (show ρ ∈ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1} | 1 / 2 < ρ.val.re ∧ 1 / 2 < |ρ.val.im|}
          from ⟨hr, lt_of_not_ge hi⟩)]
      ring
  · rw [Set.indicator_of_notMem (show ρ ∉ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1} | 1 / 2 < ρ.val.re} from hr),
      Set.indicator_of_notMem (show ρ ∉ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1} | 1 / 2 < ρ.val.re ∧ |ρ.val.im| ≤ 1 / 2}
        from fun h => hr h.1),
      Set.indicator_of_notMem (show ρ ∉ {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1} | 1 / 2 < ρ.val.re ∧ 1 / 2 < |ρ.val.im|}
        from fun h => hr h.1)]
    ring

/-- LEAF. Low sub-band of the upper half.  On the zeros of `L χ` in the strip with
`|im ρ| ≤ 1 / 2` and `1 / 2 < re ρ`, the multiplicity-weighted squared Mellin mass is at
most a quarter of the squared `L2` energy `Sec45.nTwo`.  The index set is a sub-band of the
half-strip of the target, so the sum has strictly fewer terms, and the constant is a
quarter instead of a half; it says nothing about the zeros of the half-strip whose height
exceeds `1 / 2`. -/
theorem leaf_upper_half_low_height_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | 1 / 2 < ρ.val.re ∧ |ρ.val.im| ≤ 1 / 2}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 4 := by
  sorry

/-- LEAF. High sub-band of the upper half.  On the zeros of `L χ` in the strip with
`1 / 2 < |im ρ| ≤ 1` and `1 / 2 < re ρ`, the multiplicity-weighted squared Mellin mass is
at most a quarter of the squared `L2` energy `Sec45.nTwo`.  The index set is the other
sub-band of the half-strip of the target, of the same unit-height window, and the constant
is a quarter instead of a half; it says nothing about the zeros of the half-strip with
height at most `1 / 2`. -/
theorem leaf_upper_half_high_height_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | 1 / 2 < ρ.val.re ∧ 1 / 2 < |ρ.val.im|}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 4 := by
  sorry

/-- Assembly of the split: cut the upper half of the low band at the height `1 / 2`, and
bound each of the two sub-bands by `Sec45.nTwo / 4`. -/
theorem leaf_moment_low_mass_upper_half_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1},
      Set.indicator {ρ | 1 / 2 < ρ.val.re} (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤ Sec45.nTwo / 2 := by
  classical
  rw [leaf_upper_half_mass_height_split q χ δ T]
  have h1 := leaf_upper_half_low_height_le q χ δ T
  have h2 := leaf_upper_half_high_height_le q χ δ T
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
