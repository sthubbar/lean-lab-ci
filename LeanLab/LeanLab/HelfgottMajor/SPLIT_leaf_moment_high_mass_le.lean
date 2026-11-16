import LeanLab.HelfgottMajor.SPLIT_leaf_moment_full_mass_plancherel

/-!
Split of the open target `leaf_moment_high_mass_le` of
`SPLIT_leaf_moment_full_mass_plancherel.lean`.

The target bounds the discrete Plancherel mass carried by the zeros `ρ` of `L χ` in the strip
`0 < re ρ < 1` of height `1 < |im ρ| ≤ T`, each weighted by its analytic multiplicity and the
squared Mellin norm of the Gaussian profile at `ρ`, by the log weighted energy `Sec45.nLog`,
a constant free of `q`, `δ` and `T`.

This split cuts the high band in height at the threshold `c = max 100 (4 π² |δ|)`, which is the
height above which a saddle point analysis of the Mellin transform of the Gaussian profile is
what controls the summand, and below which only a count of the zeros in a bounded box is
available.

- Below `c` the band `1 < |im ρ| ≤ c` is a sum over the zeros of a box whose height is fixed by
  `δ` and does not grow with `T`; what it needs is a count of the zeros with `|im ρ| ≤ c`, which
  grows like `c log q / (2 π)`, against the size of the Mellin transform on that box.
- Above `c` the band `c < |im ρ| ≤ T` is a sum over zeros of unbounded height, and there the
  squared Mellin norm is small of exponential order in the height, so the band is controlled by
  the exponential decay summed against the zero density, not by the count; the window cutoff
  `|im ρ| ≤ T` only truncates it.

Each leaf is one of those two band bounds, with half of the budget `Sec45.nLog`, and each is a
sub-sum of the target's sum, so neither leaf contains the target.  The assembly
`leaf_moment_high_mass_le_split` below is the pointwise partition
`1 = indicator(low box) + indicator(tall range)` on the band `1 < |im ρ|`, and uses only the two
leaves and no `sorry`.

Diagnostic value of the cut: the two leaves separate the two mechanisms that the constant
`Sec45.nLog` has to beat at once, and they put the whole conductor dependence of the target in
the bounded-height leaf, since only the count of the zeros in a box of fixed height grows with
`q`.  A prover of the tall leaf needs the exponential decay of the Mellin transform in the
height, which is available as an envelope bound; a prover of the bounded-height leaf needs the
zero count in the box and must then reconcile that count with a right side free of `q`.

Degenerate values, checked before the leaves were kept.  `T ≤ 1` makes the index set
`|im ρ| ≤ T` meet the band `1 < |im ρ|` in no point, so every sum here is the empty sum `0` and
both leaves hold trivially; `δ = 0` gives `c = 100` and no `δ`-dependent term survives anywhere;
a negative `δ` enters only through `|δ|`; a window holding no zero gives `0` on the left against
the positive constants `Sec45.nLog / 2`; the threshold is at least `100 > 1`, so the band really
is split and neither piece is empty by construction; no division occurs, and the only coercion
is the multiplicity, a natural number, cast to `ℝ`.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- LEAF. Bounded-height band.  The part of the high band `1 < |im ρ| ≤ T` carried by the zeros
whose height is at most the threshold `max 100 (4 π² |δ|)` is at most half of the log weighted
energy `Sec45.nLog`.  The height box of this band is fixed by `δ` and carries no `T`; the
estimate is a count of the zeros of that box against the size of the Mellin transform there.
It says nothing about the zeros taller than the threshold. -/
theorem leaf_high_mass_bounded_height_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)} ∩
          {ρ | |ρ.val.im| ≤ 1}ᶜ)
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nLog / 2 := by
  sorry

/-- LEAF. Tall band.  The part of the high band `1 < |im ρ| ≤ T` carried by the zeros whose
height exceeds the threshold `max 100 (4 π² |δ|)` is at most half of the log weighted energy
`Sec45.nLog`.  Above the threshold the Mellin transform is of exponential size in the height,
so the band is the decay summed against the zero density, with the window cutoff `|im ρ| ≤ T`
only truncating the sum.  It says nothing about the zeros of height at most the threshold. -/
theorem leaf_high_mass_tall_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | max 100 (4 * π ^ 2 * |δ|) < |ρ.val.im|} ∩
          {ρ | |ρ.val.im| ≤ 1}ᶜ)
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nLog / 2 := by
  sorry

/-- Assembly of the split: on the band `1 < |im ρ|` the indicator of the whole band is the sum
of the indicators of the bounded-height box and of the tall range, so the target's sum is the
sum of the two band sums; bounding each band by half of `Sec45.nLog` and adding gives the
target. -/
theorem leaf_moment_high_mass_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤ Sec45.nLog := by
  classical
  set c : ℝ := max 100 (4 * π ^ 2 * |δ|) with hc
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T} := (leaf_moment_window_finite q χ T).fintype
  have hsplit :
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
        = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
              |ρ.im| ≤ T},
            Set.indicator ({ρ | |ρ.val.im| ≤ c} ∩
                {ρ | |ρ.val.im| ≤ 1}ᶜ)
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
          + (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
                ρ.re < 1 ∧ |ρ.im| ≤ T},
              Set.indicator ({ρ | c < |ρ.val.im|} ∩
                  {ρ | |ρ.val.im| ≤ 1}ᶜ)
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                  ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
    rw [tsum_fintype, tsum_fintype, tsum_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ρ _
    simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
    by_cases h1 : |(ρ : ℂ).im| ≤ 1
    · simp [h1]
    · have h1' : ¬ |(ρ : ℂ).im| ≤ 1 := h1
      by_cases h2 : |(ρ : ℂ).im| ≤ c
      · have h2' : ¬ c < |(ρ : ℂ).im| := not_lt.mpr h2
        simp [h1', h2, h2']
      · have h2' : c < |(ρ : ℂ).im| := not_le.mp h2
        simp [h1', h2, h2']
  rw [hsplit]
  refine le_trans (add_le_add (leaf_high_mass_bounded_height_le q χ δ T)
    (leaf_high_mass_tall_le q χ δ T)) ?_
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
