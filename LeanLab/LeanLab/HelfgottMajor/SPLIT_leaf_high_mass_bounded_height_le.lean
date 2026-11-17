import LeanLab.HelfgottMajor.SPLIT_leaf_moment_high_mass_le

/-!
Split of the open leaf `leaf_high_mass_bounded_height_le` of
`SPLIT_leaf_moment_high_mass_le.lean`.

The target bounds the discrete Plancherel mass carried by the zeros `ρ` of `L χ` in the strip
`0 < re ρ < 1` with height `1 < |im ρ| ≤ T` and height at most the threshold
`c = max 100 (4 π² |δ|)`, each zero weighted by its analytic multiplicity and the squared
Mellin norm of the Gaussian profile at `ρ`, by half of the log weighted energy `Sec45.nLog`.

The threshold is at least `100`, so the height box of the target is the union of two disjoint
boxes: the box `1 < |im ρ| ≤ 100`, whose height is the absolute constant `100`, and the box
`100 < |im ρ| ≤ c`, whose height grows with `|δ|` and which is empty whenever
`4 π² |δ| ≤ 100`.  Those two boxes are the two mechanisms inside the target.  In the first one
the height of the zero box does not depend on `δ` at all, so what the sum needs there is only
the number of zeros of a box of that fixed height against the size of the Mellin transform on
it.  In the second one the box is the one selected by the Gaussian profile itself, and the sum
is the profile's decay sampled at the zeros of that box.

The split therefore has two leaves, one for each box, and each with half of the target's right
side, `Sec45.nLog / 4`.  Each leaf is about a proper sub-sum of the target, so neither contains
the target.  The assembly `leaf_high_mass_bounded_height_le_split` below is the pointwise
partition `1 = indicator(absolute height box) + indicator(δ selected box)` on the band
`1 < |im ρ|`, and uses only the two leaves and no `sorry`.

Degenerate values, checked before the leaves were kept.  `T ≤ 1` makes the index set meet the
band `1 < |im ρ|` in no point, so every sum here is the empty sum `0` and both leaves hold;
a window holding no zero gives `0` on the left of each leaf against a positive right side;
`δ = 0` gives `c = 100`, so the second box is empty and its leaf reads `0 ≤ Sec45.nLog / 4`,
while the first box is `{|im ρ| ≤ 100}` and the partition loses no case; a negative `δ` enters
only through `|δ|`; the threshold satisfies `100 ≤ c`, so the two boxes really do cover the
target's box; no division by a variable occurs, `2` and `4` are nonzero literals, and the only
coercion is the multiplicity, a natural number, cast to `ℝ`.  Splitting `Sec45.nLog / 2` into
two quarters is exact in `ℝ`, so the addition in the assembly loses nothing.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- LEAF. Absolute height box.  The part of the target's box with absolute height
`1 < |im ρ| ≤ 100` is at most a quarter of the log weighted energy `Sec45.nLog`.  The height of
this box is the absolute constant `100` and does not depend on `δ`, so the estimate needs only
the number of zeros in a box of that fixed height against the size of the Mellin transform
there; it says nothing about the zeros above height `100`. -/
theorem leaf_high_mass_absolute_box_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | |ρ.val.im| ≤ 100} ∩ {ρ | |ρ.val.im| ≤ 1}ᶜ)
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nLog / 4 := by
  sorry

/-- LEAF. `δ` selected box.  The part of the target's box with height in
`100 < |im ρ| ≤ max 100 (4 π² |δ|)` is at most a quarter of the log weighted energy
`Sec45.nLog`.  This box is empty unless `4 π² |δ| > 100`, so the leaf is vacuous for small
`δ` and carries content only for the `δ` for which the Gaussian profile selects a box above
height `100`; it says nothing about the zeros of height at most `100`. -/
theorem leaf_high_mass_delta_box_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | 100 < |ρ.val.im|} ∩
          {ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nLog / 4 := by
  sorry

/-- Assembly of the split: on the band `1 < |im ρ|` the indicator of the target's box
`|im ρ| ≤ max 100 (4 π² |δ|)` is the sum of the indicators of the absolute height box
`|im ρ| ≤ 100` and of the `δ` selected box `100 < |im ρ| ≤ max 100 (4 π² |δ|)`, since the
threshold is at least `100`; so the target's sum is the sum of the two box sums, and bounding
each box sum by a quarter of `Sec45.nLog` and adding gives the target. -/
theorem leaf_high_mass_bounded_height_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T}, Set.indicator ({ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)} ∩ {ρ | |ρ.val.im| ≤ 1}ᶜ) (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤ Sec45.nLog / 2 := by
  classical
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T} := (leaf_moment_window_finite q χ T).fintype
  have hc : (100 : ℝ) ≤ max 100 (4 * π ^ 2 * |δ|) := le_max_left _ _
  have hsplit :
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator ({ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)} ∩
            {ρ | |ρ.val.im| ≤ 1}ᶜ)
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
        = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
              |ρ.im| ≤ T},
            Set.indicator ({ρ | |ρ.val.im| ≤ 100} ∩ {ρ | |ρ.val.im| ≤ 1}ᶜ)
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
          + (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
                ρ.re < 1 ∧ |ρ.im| ≤ T},
              Set.indicator ({ρ | 100 < |ρ.val.im|} ∩
                  {ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)})
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                  ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
    rw [tsum_fintype, tsum_fintype, tsum_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ρ _
    simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
    by_cases h1 : |(ρ.val : ℂ).im| ≤ 1
    · have h2 : ¬ (100 : ℝ) < |(ρ.val : ℂ).im| := by linarith
      have h3 : |(ρ.val : ℂ).im| ≤ 100 := by linarith
      have h4 : |(ρ.val : ℂ).im| ≤ max 100 (4 * π ^ 2 * |δ|) := le_trans h3 hc
      simp [h1, h2, h3, h4]
    · by_cases h2 : |(ρ.val : ℂ).im| ≤ 100
      · have h2' : ¬ (100 : ℝ) < |(ρ.val : ℂ).im| := not_lt.mpr h2
        have h4 : |(ρ.val : ℂ).im| ≤ max 100 (4 * π ^ 2 * |δ|) := le_trans h2 hc
        simp [h1, h2, h2', h4]
      · have h2' : (100 : ℝ) < |(ρ.val : ℂ).im| := not_le.mp h2
        by_cases h3 : |(ρ.val : ℂ).im| ≤ max 100 (4 * π ^ 2 * |δ|)
        · simp [h1, h2, h2', h3]
        · simp [h1, h2, h2', h3]
  rw [hsplit]
  linarith [leaf_high_mass_absolute_box_le q χ δ T, leaf_high_mass_delta_box_le q χ δ T]

end LeanLab.HelfgottMajor.DecompJ1153
