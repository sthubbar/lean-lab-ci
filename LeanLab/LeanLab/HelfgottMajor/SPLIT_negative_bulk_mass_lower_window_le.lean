import LeanLab.HelfgottMajor.SPLIT_negative_bulk_mass_window_le

/-!
Split of `negative_bulk_mass_lower_window_le` in
`LeanLab.HelfgottMajor.SPLIT_negative_bulk_mass_window_le` into three leaves.

The statement being split bounds the multiplicity weighted Mellin mass attached to the negative
zeros whose ordinate lies in the closed window from minus two to minus seven quarters, for a
Dirichlet `L`-function in the strip `0 < re < 1` and below height `T`, by half of the mean weight
integral over `[1, T]` together with three eighths of the shifted log weight integral.

The split cuts the window at minus fifteen eighths. The two pieces are charged to different
mechanisms inside the two budgets of the sealed statement. The far piece, from minus two up to
minus fifteen eighths, sits against the height at which the Gaussian profile starts to decay, and it
is paid out of the sliver of the shifted log weight integral alone, in the amount three sixteenths
of it: the same decay argument that pays the tail past height two in the parent split, applied to
the last eighth of the window. The near piece, from minus fifteen eighths up to minus seven
quarters, sits against the reference height of the parent split, where the profile is at its
fullest, so it keeps half of the mean weight integral and is charged to the remaining three
sixteenths of the shifted log weight integral.

Three sixteenths plus three sixteenths is three eighths, and the mean weight integral is spent once,
so the two budgets add up to the budget of the sealed statement. The volume of the far piece is
strictly smaller than the volume of the window and it carries no mean weight integral at all; the
volume of the near piece is strictly smaller than the volume of the window and it carries half of
the shifted log weight integral. The assembly is the partition of the ordinate window at minus
fifteen eighths, the addition of the two inequalities, and the arithmetic of the budgets. It has no
sorry of its own. All three leaves are OPEN.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform

/-- LEAF 1 of 3, the partition of the window at minus fifteen eighths. The mass over the closed
window from minus two to minus seven quarters equals the mass over the part of the window at
ordinate at most minus fifteen eighths plus the mass over the part of the window strictly above
minus fifteen eighths. The two pieces are disjoint and their union is the window, because the
height condition of modulus at most two is carried by all three sets, and the mass is a sum over a
set of ordinates. This is bookkeeping only: it asserts no bound and no estimate. -/
theorem negative_bulk_mass_lower_window_partition (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) =
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(15 / 8) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(15 / 8) < ρ.val.im ∧ ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) := by
  -- Required: the pointwise disjoint union of the two indicator sets and the additivity of the sum
  -- over the zero set of the strip below height `T`.
  sorry

/-- LEAF 2 of 3, the far eighth of the window, from minus two up to minus fifteen eighths. The mass
over that piece is at most three sixteenths of the shifted log weight integral over the height
interval, and carries no mean weight integral at all. This is the piece at the edge of the decay
region of the Gaussian profile, so the decay of the profile past this height pays for the bounded
number of ordinates it holds. -/
theorem negative_bulk_mass_lower_window_far_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(15 / 8) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (3 / 16) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  -- Required: the already decayed profile on the last eighth of the window, an explicit count of
  -- the ordinates it holds, and a pointwise envelope for the mass charged to the shifted log weight
  -- integral alone.
  sorry

/-- LEAF 3 of 3, the near piece of the window, strictly above minus fifteen eighths and at most
minus seven quarters. The mass over that piece is at most half of the mean weight integral over the
height interval plus three sixteenths of the shifted log weight integral. The piece sits against
the reference height of the parent split where the profile is at its fullest, so the mean weight
integral pays for half of it and only three sixteenths of the shifted log weight integral is spent
on the rest. -/
theorem negative_bulk_mass_lower_window_near_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(15 / 8) < ρ.val.im ∧ ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) +
      (3 / 16) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  -- Required: an explicit count of the ordinates in this piece together with a pointwise envelope
  -- for the mass on it, charged to half of the mean weight and three sixteenths of the shifted log
  -- weight.
  sorry

/-- The statement of `negative_bulk_mass_lower_window_le`, assembled from the three leaves: the
window mass splits at minus fifteen eighths into the mass of the far eighth and the mass of the near
piece, the far eighth is paid out of three sixteenths of the shifted log weight integral, the near
piece keeps half of the mean weight integral and the remaining three sixteenths of the shifted log
weight integral, and the two sixteenths shares add up to the three eighths of the statement. -/
theorem negative_bulk_mass_lower_window_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) +
      (3 / 8) * (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  have harith : ∀ A B : ℝ,
      (3 / 16) * B + ((1 / 2) * A + (3 / 16) * B) = (1 / 2) * A + (3 / 8) * B := by
    intro A B
    ring
  have hpart := negative_bulk_mass_lower_window_partition q χ δ T hT
  have hfar := negative_bulk_mass_lower_window_far_le q χ δ T hT
  have hnear := negative_bulk_mass_lower_window_near_le q χ δ T hT
  calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ)
      = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(15 / 8) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(15 / 8) < ρ.val.im ∧ ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) := hpart
    _ ≤ ((3 / 16) * (∫ t in (1 : ℝ)..T,
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              (0.15 * log ((q : ℝ) * t) + 3.389))) +
        ((1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
            ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              log ((q : ℝ) * t / (2 * π)))) +
          (3 / 16) * (∫ t in (1 : ℝ)..T,
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              (0.15 * log ((q : ℝ) * t) + 3.389))) := add_le_add hfar hnear
    _ = (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
            log ((q : ℝ) * t / (2 * π)))) +
        (3 / 8) * (∫ t in (1 : ℝ)..T,
          ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
            (0.15 * log ((q : ℝ) * t) + 3.389)) :=
      harith _ _

end LeanLab.HelfgottMajor.Decomp431a
