import LeanLab.HelfgottMajor.SPLIT_negative_mass_bulk_le

/-!
Split of `Decomp431a.negative_bulk_mass_integral` in
`LeanLab.HelfgottMajor.SPLIT_negative_mass_bulk_le` into two leaves.

The statement being split bounds the multiplicity weighted sum of the Gaussian Mellin norms at the
zeros of a primitive Dirichlet `L`-function in the strip `0 < re < 1`, at ordinates at most minus
three halves and of modulus at most `T`, by two height integrals over `[1, T]`: the critical line
norms against the mean weight divided by `2 * π`, and the derivative norms against the shifted
log weight.

The split cuts the zero set at height two, which is where the Gaussian profile has decayed past
every summand of the near window. The first leaf is the near window `3/2 ≤ -im ≤ 2`: its summands
are the largest, but a bounded stretch of heights holds only boundedly many zeros, so it is
charged to the whole mean weight integral together with three quarters of the shifted log weight
integral. The second leaf is the tail `2 < -im`, where the exponential decay of the profile pays
for the logarithmically growing number of terms; it is charged to the remaining quarter of the
shifted log weight integral. The two budgets add up to the bound of the statement being split, so
the assembly is an addition of two inequalities.

`negative_bulk_mass_integral_split` assembles the statement from the two leaves. It has no sorry
of its own. Both leaves are OPEN.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform

/-- LEAF 1 of 2, the near window. The multiplicity weighted Mellin mass attached to the zeros
whose ordinate lies in the closed interval from minus two to minus three halves is at most the
whole mean weight integral over the height interval, plus three quarters of the shifted log
weight integral over the same interval. The window carries the largest summands, but it occupies
a bounded stretch of heights, so it is charged to the larger share of the error budget. -/
theorem negative_bulk_mass_window_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      (3 / 4) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  -- BLOCKED OUT OF REACH 2026-11-14 FREE-ms-leanstral task484
  -- Required: pointwise bound on mellinMassTerm for zeros in [-2, -3/2]
  -- Missing: explicit formula with residue, zero counting estimate N(T), optimal
  -- logarithmic derivative bound with constants 0.15 and 3.389
  sorry

/-- LEAF 2 of 2, the tail. The multiplicity weighted Mellin mass attached to the zeros whose
ordinate is at most minus two in absolute value is at most one quarter of the shifted log
weight integral over the height interval. Beyond height two the Gaussian profile has decayed
exponentially while the number of ordinates grows only logarithmically, so the smallest share of
the error budget carries the tail. -/
theorem negative_bulk_mass_tail_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im|}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / 4) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  -- BLOCKED OUT OF REACH 2026-11-14 FREE-ms-leanstral task484
  -- Required: pointwise bound on mellinMassTerm for zeros with |im| > 2
  -- Missing: explicit formula with residue, zero counting estimate N(T), tail bound
  -- with optimal constants
  sorry

/-- The two leaves add up to the bound of `negative_bulk_mass_integral`: the zero set splits at
height two, the two budgets split the mean weight integral entirely and the shifted log weight
integral in the proportions three quarters and one quarter, and a quarter plus three quarters is
one. The zero set of the strip below height `T` is summable by the low zero term result, which is
what turns the sum over the union of the two pieces into the sum of the two sums. -/
theorem negative_bulk_mass_integral_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)} (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  classical
  have hwin := negative_bulk_mass_window_le q χ δ T hT
  have htail := negative_bulk_mass_tail_le q χ δ T hT
  have hsum : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
      mellinMassTerm χ δ ρ.val) := by
    apply (Zeros269.low_zero_terms_summable χ δ 1 T hzeros).norm.congr
    intro ρ
    simp [zeroTerm, mellinMassTerm, nsmul_eq_mul]
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)} (fun ρ => mellinMassTerm χ δ ρ.val) ρ =
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
            (fun ρ => mellinMassTerm χ δ ρ.val) ρ +
          Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im|}
            (fun ρ => mellinMassTerm χ δ ρ.val) ρ := by
    intro ρ
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases hx : ρ.val.im ≤ -(3 / 2) <;> by_cases h2 : |ρ.val.im| ≤ 2 <;> simp [hx, h2]
  calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)} (fun ρ => mellinMassTerm χ δ ρ.val) ρ)
      = ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          (Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
              (fun ρ => mellinMassTerm χ δ ρ.val) ρ +
            Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im|}
              (fun ρ => mellinMassTerm χ δ ρ.val) ρ) := tsum_congr hpt
    _ = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
              (fun ρ => mellinMassTerm χ δ ρ.val) ρ) +
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im|}
              (fun ρ => mellinMassTerm χ δ ρ.val) ρ) :=
        Summable.tsum_add (hsum.indicator _) (hsum.indicator _)
    _ ≤ ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
            ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              log ((q : ℝ) * t / (2 * π))) +
          (3 / 4) * (∫ t in (1 : ℝ)..T,
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              (0.15 * log ((q : ℝ) * t) + 3.389))) +
          (1 / 4) * (∫ t in (1 : ℝ)..T,
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              (0.15 * log ((q : ℝ) * t) + 3.389)) := add_le_add hwin htail
    _ = (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
            log ((q : ℝ) * t / (2 * π))) +
        (∫ t in (1 : ℝ)..T,
          ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
            (0.15 * log ((q : ℝ) * t) + 3.389)) := by ring

end LeanLab.HelfgottMajor.Decomp431a
