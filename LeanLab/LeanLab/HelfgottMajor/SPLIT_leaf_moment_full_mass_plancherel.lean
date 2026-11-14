import LeanLab.HelfgottMajor.SPLIT_leaf_moment_plancherel_bound

/-!
Split of the open target `leaf_moment_full_mass_plancherel` of
`SPLIT_leaf_moment_plancherel_bound.lean`.

The target bounds the discrete Plancherel mass

`∑ (multiplicity of ρ) * ‖gaussianMellin δ ρ‖ ^ 2`

over the zeros `ρ` of `L χ` in the strip `0 < re ρ < 1` with `|im ρ| ≤ T` by the two
closed forms `Sec45.nTwo` and `Sec45.nLog`, with no dependence on the conductor `q`.

The split cuts the index set at the fixed height `|im ρ| ≤ 1`.  The windows in play are
finite, so both sides of the cut are honest finite sums and the total mass is the sum of
the two band masses.  Each band is then bounded by one of the two energy constants: the
low band `|im ρ| ≤ 1` by `Sec45.nTwo`, and the high band `1 < |im ρ| ≤ T` by
`Sec45.nLog`.  Adding the two bounds gives the target.  Each step is a separate leaf
ending in `sorry`; the assembly `leaf_moment_full_mass_plancherel_split` below uses only
those leaves and no `sorry`.

Diagnostic value of the cut: the low band is the piece that the zero count of the strip
drives, since the zeros with `|im ρ| ≤ 1` number about `log q / π`; the high band is the
piece that the Mellin decay of the Gaussian profile drives.  The low leaf therefore
isolates the whole `q` dependence of the target.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- LEAF. Finiteness of the zero window.  The zeros of `L χ` in the strip `0 < re < 1`
with `|im| ≤ T` are the intersection of the strip box with the zero set of `L χ`, which is
discrete after removing the possible pole at `s = 1`; a closed bounded box meets a discrete
set finitely.  This leaf only supplies the `Fintype` instance that turns the two band sums
into finite sums; it estimates nothing about the sizes of the summands. -/
theorem leaf_moment_window_finite (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.Finite := by
  sorry

/-- LEAF. Low band mass.  The part of the zero mass carried by the zeros with
`|im ρ| ≤ 1` is at most the squared `L2` energy `Sec45.nTwo` of the Gaussian profile.  The
height cutoff at `1` fixes the band once and for all, so the band sum is a sum over the
finitely many zeros in a fixed box, each weighted by its multiplicity and its squared Mellin
norm.  It says nothing about the zeros above height `1`. -/
theorem leaf_moment_low_mass_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo := by
  sorry

/-- LEAF. High band mass.  The part of the zero mass carried by the zeros with
`1 < |im ρ| ≤ T` is at most the log-weighted squared `L2` energy `Sec45.nLog` of the
Gaussian profile.  The band excludes the finitely many zeros of height at most `1`, so the
summands are controlled by the decay of the Mellin transform in the height, which is what
`Sec45.nLog` measures.  This leaf says nothing about the band `|im ρ| ≤ 1`. -/
theorem leaf_moment_high_mass_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nLog := by
  sorry

/-- Assembly of the split: the window is finite, so the zero mass is the sum of its low
band `|im ρ| ≤ 1` and its high band `1 < |im ρ| ≤ T`; bounding the two bands by
`Sec45.nTwo` and `Sec45.nLog` gives the target. -/
theorem leaf_moment_full_mass_plancherel_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2) ≤
    Sec45.nTwo + Sec45.nLog := by
  classical
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T} := (leaf_moment_window_finite q χ T).fintype
  have hsplit :
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2)
        = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
              ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | |ρ.val.im| ≤ 1}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
          + (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
                ρ.re < 1 ∧ |ρ.im| ≤ T},
              Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                  ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
    rw [tsum_fintype, tsum_fintype, tsum_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ρ _
    by_cases h : |(ρ : ℂ).im| ≤ 1
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  rw [hsplit]
  have hlow := leaf_moment_low_mass_le q χ δ T
  have hhigh := leaf_moment_high_mass_le q χ δ T
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
