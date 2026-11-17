import LeanLab.HelfgottMajor.SPLIT_negative_bulk_mass_window_le

/-!
Split of `negative_bulk_mass_upper_window_le` in
`LeanLab.HelfgottMajor.SPLIT_negative_bulk_mass_window_le` into three leaves.

The statement being split bounds the multiplicity weighted Mellin mass attached to the negative
zeros whose ordinate lies in the quarter window from minus seven quarters to minus three halves,
for a Dirichlet `L`-function in the strip `0 < re < 1` and below height `T`, by half of the mean
weight integral over `[1, T]` together with three eighths of the shifted log weight integral.

The split cuts that quarter window at minus thirteen eighths, its own midpoint. The window occupies
a bounded stretch of heights, so only boundedly many ordinates lie in it; the statement being split
pays the whole quarter out of half of the mean weight budget and three eighths of the shifted log
weight budget, and here each half of the quarter pays out of half of each of those budgets, that is
out of a quarter of the mean weight integral and three sixteenths of the shifted log weight
integral. Halving a bounded window leaves the reason for the bound unchanged on either half, so
each half is strictly easier than the quarter: it carries less mass against a smaller budget.

The two leaf bounds add up to the bound of the statement being split, because a quarter plus a
quarter of the mean weight integral is half of it and three sixteenths plus three sixteenths of the
shifted log weight integral is three eighths of it. The assembly is the partition identity for the
two halves of the quarter, then the addition of the two half inequalities, then the arithmetic of
the budgets. It has no sorry of its own. All three leaves are OPEN.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform

/-- LEAF 1 of 3, the partition of the quarter window at its midpoint minus thirteen eighths. The
mass over the window from above minus seven quarters to minus three halves equals the mass over
the part of the window at ordinate at most minus thirteen eighths plus the mass over the part
above minus thirteen eighths. The two pieces are disjoint and cover the window, and the mass is
finitely supported on the bounded height range, which is what turns the sum over the union into
the sum of the two sums. This is bookkeeping only: it asserts no bound and no estimate. -/
theorem negative_bulk_mass_upper_window_quarter_partition
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) =
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(13 / 8) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(13 / 8) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) := by
  -- Required: finiteness of the ordinate set in a bounded height range and additivity of the
  -- sum over a disjoint union of two indicator sets.
  sorry

/-- LEAF 2 of 3, the lower half of the quarter window, from above minus seven quarters to minus
thirteen eighths. The mass over that half is at most a quarter of the mean weight integral over
the height interval plus three sixteenths of the shifted log weight integral over the same
interval. The half window occupies a bounded stretch of heights and therefore carries only
boundedly many ordinates, so a quarter of each of the two budgets pays for it with room to
spare. -/
theorem negative_bulk_mass_upper_window_quarter_low_le
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(13 / 8) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) +
      (3 / 16) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  -- Required: an explicit count of the ordinates in a bounded height range together with a
  -- pointwise envelope for the mass on that range, charged against a quarter of each budget.
  sorry

/-- LEAF 3 of 3, the upper half of the quarter window, above minus thirteen eighths and at most
minus three halves. The mass over that half is at most the other quarter of the mean weight
integral over the height interval plus the other three sixteenths of the shifted log weight
integral over the same interval. This piece is adjacent to the reference height of the statement
being split, and being a bounded stretch of heights it again carries only boundedly many
ordinates. -/
theorem negative_bulk_mass_upper_window_quarter_high_le
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(13 / 8) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) +
      (3 / 16) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  -- Required: the same count and pointwise envelope as the lower half, on the piece of the window
  -- nearest the reference height, charged against the same quarter budgets.
  sorry

/-- The statement of `negative_bulk_mass_upper_window_le`, assembled from the three leaves: the
quarter window mass splits into the mass of its two halves, each half is bounded by a quarter of
the mean weight integral plus three sixteenths of the shifted log weight integral, and the sum of
those two half budgets is the budget of the statement. -/
theorem negative_bulk_mass_upper_window_le_split
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) +
      (3 / 8) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  have harith : ∀ A B : ℝ,
      ((1 / 4) * A + (3 / 16) * B) + ((1 / 4) * A + (3 / 16) * B) =
        (1 / 2) * A + (3 / 8) * B := by
    intro A B
    ring
  have hpart := negative_bulk_mass_upper_window_quarter_partition q χ δ T hT
  have hlow := negative_bulk_mass_upper_window_quarter_low_le q χ δ T hT
  have hhigh := negative_bulk_mass_upper_window_quarter_high_le q χ δ T hT
  calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ)
      = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(13 / 8) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(13 / 8) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) := hpart
    _ ≤ ((1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
            ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              log ((q : ℝ) * t / (2 * π)))) +
          (3 / 16) * (∫ t in (1 : ℝ)..T,
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              (0.15 * log ((q : ℝ) * t) + 3.389))) +
        ((1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
            ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              log ((q : ℝ) * t / (2 * π)))) +
          (3 / 16) * (∫ t in (1 : ℝ)..T,
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              (0.15 * log ((q : ℝ) * t) + 3.389))) := add_le_add hlow hhigh
    _ = (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
            log ((q : ℝ) * t / (2 * π)))) +
        (3 / 8) * (∫ t in (1 : ℝ)..T,
          ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
            (0.15 * log ((q : ℝ) * t) + 3.389)) := harith _ _

end LeanLab.HelfgottMajor.Decomp431a
