import LeanLab.HelfgottMajor.SPLIT_tail_mass_integral

/-!
Splitting the Gaussian counting step `Decomp269c.gaussian_count_le_integral` into three
smaller steps.

The step bounds the total Gaussian weight of the zeros of `L(s, χ)` inside the critical
strip above height `T` by the density weighted Gaussian integral `gaussianTailIntegral`.

The split separates

* the zero shift case, where the branch is absent and both sides vanish identically,
* the summability of the Gaussian weights over those zeros at nonzero shift,
* the comparison of the total weight with the density weighted Gaussian integral,

and `gaussian_count_le_integral_split` assembles them. The assembly does no analysis: it
decides the shift, discharges the guard `if δ = 0` in the summand by `if_neg`, and transfers
summability and the total across that identification. Hence each step is one inequality, one
summability statement or one case, all strictly weaker than the assembled statement.

The branch at zero shift is the one place where the two sides must be compared with the
junk-value convention in mind: `gaussianTailIntegral q 0 T` is `0` by its guard and the
summand is `0` as well, so the comparison is `0 ≤ 0` and not an appeal to the integral.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- LEAF. The zero shift case of the Gaussian counting step: at `δ = 0` every summand of the
series is `0`, so the series is summable with total `0`, and the density weighted Gaussian
integral is `0` by its own guard. This gives the whole statement at zero shift and carries no
height hypothesis, since neither side depends on `T` there. -/
theorem gaussian_count_zero_shift (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hδ : δ = 0) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ≤
      gaussianTailIntegral q δ T := by
  subst hδ
  have hz : (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
        if (0 : ℝ) = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |0|)) ^ 2))
      = fun _ => (0 : ℝ) := by
    funext ρ
    simp
  have hg : gaussianTailIntegral q 0 T = 0 := by
    simp [gaussianTailIntegral]
  rw [hz, hg]
  exact ⟨summable_zero, by simp⟩

/-- LEAF. Summability at nonzero shift: the Gaussian weights of the strip zeros above height
`T` form a summable family. This is the counting input for the branch, with the absolute
convergence coming from the density of the zeros against the Gaussian decay; it says nothing
about the size of the total. -/
theorem gaussian_count_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hδ : δ ≠ 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
  sorry

/-- LEAF. The comparison at nonzero shift: the total Gaussian weight of the strip zeros above
height `T` is at most the density weighted Gaussian tail integral. This is the quantitative
half of the branch, and it takes the summability of the weights as a hypothesis so that it is
only the size of the total. -/
theorem gaussian_count_tsum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hδ : δ ≠ 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ≤
      gaussianTailIntegral q δ T := by
  sorry

/-- The Gaussian counting step, assembled from the three smaller steps. At zero shift the
first step gives the whole statement; at nonzero shift the guard in the summand is discharged
by `if_neg`, which transfers both the summability and the value of the series to the plain
Gaussian weights, and the second and third steps close the two components. -/
theorem gaussian_count_le_integral_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ≤
      gaussianTailIntegral q δ T := by
  classical
  by_cases hδ : δ = 0
  · exact gaussian_count_zero_shift q χ δ T hδ
  · have hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) :=
      gaussian_count_summable q χ δ T hδ hT
    have hguard : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) =
          exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2) := fun ρ => if_neg hδ
    refine ⟨(summable_congr hguard).mpr hs, ?_⟩
    rw [tsum_congr hguard]
    exact gaussian_count_tsum_le q χ δ T hδ hT hs

end LeanLab.HelfgottMajor.Decomp269c
