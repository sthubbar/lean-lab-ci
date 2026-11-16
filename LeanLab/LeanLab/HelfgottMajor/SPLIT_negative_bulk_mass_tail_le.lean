import LeanLab.HelfgottMajor.SPLIT_negative_bulk_mass_integral

/-!
Split of `negative_bulk_mass_tail_le` of `LeanLab.HelfgottMajor.SPLIT_negative_bulk_mass_integral`
into two leaves.

The statement being split bounds the multiplicity weighted sum of the Gaussian Mellin norms at the
zeros of a Dirichlet `L`-function in the strip `0 < re < 1`, with ordinate at most minus three
halves and of modulus larger than two, by one quarter of the height integral over `[1, T]` of the
derivative norms against the shifted log weight.

The tail is cut once, at the height `2 + sqrt (log (q * T + 1))`, which is the height at which the
growth of the number of ordinates, of size `log (q * T)`, stops being able to pay for the decay of
the Gaussian profile along the line. Below the cut the ordinates are a bounded stretch of heights
counted from the cut at two, and the summands there are the largest of the tail; above the cut the
profile has decayed into the region where the count is sublinear in the height. Each of the two
slabs is charged one eighth of the derivative weight integral, so each leaf is a strictly weaker
version of the target: its index set is a proper piece of the target's index set and its budget is
half of the target's. The two budgets add up to the quarter of the statement being split, so the
assembly is an addition of two inequalities after the split of the indicator.

`negative_bulk_mass_tail_le_split` assembles the statement from the two leaves. It has no sorry of
its own. Both leaves are OPEN.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform

/-- LEAF 1 of 2, the near slab of the tail. The multiplicity weighted Mellin mass attached to the
zeros whose ordinate lies at most minus three halves, whose modulus is larger than two, and whose
modulus is at most the cut `2 + sqrt (log (q * T + 1))`, is at most one eighth of the derivative
weight integral over the height interval. This is the piece of the tail closest to the cut at two,
where the summands are the largest and the heights are still short on the scale `sqrt (log (q *
T + 1))`, so the count of ordinates is the elementary finite one of the strip. -/
theorem negative_bulk_mass_tail_near_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im| ∧
            |ρ.val.im| ≤ 2 + sqrt (log ((q : ℝ) * T + 1))}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / 8) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  sorry

/-- LEAF 2 of 2, the far slab of the tail. The multiplicity weighted Mellin mass attached to the
zeros whose ordinate lies at most minus three halves, whose modulus is larger than two, and whose
modulus is larger than the cut `2 + sqrt (log (q * T + 1))`, is at most one eighth of the
derivative weight integral over the height interval. Beyond the cut the Gaussian profile has
decayed past the growth of the number of ordinates, which is only logarithmic in the product of
conductor and height, so this is the slab where the decay pays for the count and where the far
end of the height interval carries the whole weight. -/
theorem negative_bulk_mass_tail_far_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im| ∧
            2 + sqrt (log ((q : ℝ) * T + 1)) < |ρ.val.im|}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / 8) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  sorry

/-- The two leaves add up to the bound of `negative_bulk_mass_tail_le`. On the index type the
indicator of the tail is the sum of the indicators of the two slabs, because a modulus of more
than two is either at most the cut or above it; the index type is finite, so the sum over it
splits into the two sums; and one eighth plus one eighth is one quarter. -/
theorem negative_bulk_mass_tail_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im|}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / 4) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  classical
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) :=
    ZeroCount1623.summable_zeroIdx χ T _
  have hnear := negative_bulk_mass_tail_near_le q χ δ T hT
  have hfar := negative_bulk_mass_tail_far_le q χ δ T hT
  have hpt : ∀ x : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im|}
          (fun ρ => mellinMassTerm χ δ ρ.val) x =
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im| ∧
            |ρ.val.im| ≤ 2 + sqrt (log ((q : ℝ) * T + 1))}
            (fun ρ => mellinMassTerm χ δ ρ.val) x +
          Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im| ∧
            2 + sqrt (log ((q : ℝ) * T + 1)) < |ρ.val.im|}
            (fun ρ => mellinMassTerm χ δ ρ.val) x := by
    intro x
    by_cases h : x.val.im ≤ -(3 / 2) ∧ 2 < |x.val.im|
    · obtain ⟨h1, h2⟩ := h
      by_cases h3 : |x.val.im| ≤ 2 + sqrt (log ((q : ℝ) * T + 1))
      · have h3' : ¬ 2 + sqrt (log ((q : ℝ) * T + 1)) < |x.val.im| := not_lt.mpr h3
        simp [Set.indicator, h1, h2, h3, h3']
      · have h3' : 2 + sqrt (log ((q : ℝ) * T + 1)) < |x.val.im| := lt_of_not_ge h3
        simp [Set.indicator, h1, h2, h3, h3']
    · rcases not_and_or.mp h with h1 | h2
      · simp [Set.indicator, h1]
      · simp [Set.indicator, h2]
  calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im|}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ)
      = ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          (Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im| ∧
              |ρ.val.im| ≤ 2 + sqrt (log ((q : ℝ) * T + 1))}
              (fun ρ => mellinMassTerm χ δ ρ.val) ρ +
            Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im| ∧
              2 + sqrt (log ((q : ℝ) * T + 1)) < |ρ.val.im|}
              (fun ρ => mellinMassTerm χ δ ρ.val) ρ) := tsum_congr hpt
    _ = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im| ∧
                |ρ.val.im| ≤ 2 + sqrt (log ((q : ℝ) * T + 1))}
              (fun ρ => mellinMassTerm χ δ ρ.val) ρ) +
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ 2 < |ρ.val.im| ∧
              2 + sqrt (log ((q : ℝ) * T + 1)) < |ρ.val.im|}
              (fun ρ => mellinMassTerm χ δ ρ.val) ρ) :=
        (hm.indicator _).tsum_add (hm.indicator _)
    _ ≤ (1 / 8) * (∫ t in (1 : ℝ)..T,
          ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
            (0.15 * log ((q : ℝ) * t) + 3.389)) +
        (1 / 8) * (∫ t in (1 : ℝ)..T,
          ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
            (0.15 * log ((q : ℝ) * t) + 3.389)) := add_le_add hnear hfar
    _ = (1 / 4) * (∫ t in (1 : ℝ)..T,
          ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
            (0.15 * log ((q : ℝ) * t) + 3.389)) := by ring

end LeanLab.HelfgottMajor.Decomp431a
