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

/-- The mass of the union of two disjoint sets is the sum of the two masses, for a summand on a
finite index type. Copy of the sibling helper in `SPLIT_negative_bulk_mass_window_le`, which is
`private` there and so not reachable from this file. -/
private lemma tsum_indicator_split_quarter {α : Type*} [Finite α] (s₁ s₂ s : Set α) (f : α → ℝ)
    (hdisj : Disjoint s₁ s₂) (hunion : s₁ ∪ s₂ = s) :
    (∑' x, s.indicator f x) = (∑' x, s₁.indicator f x) + (∑' x, s₂.indicator f x) := by
  classical
  have h₁ : Summable (fun x => s₁.indicator f x) := Summable.of_finite
  have h₂ : Summable (fun x => s₂.indicator f x) := Summable.of_finite
  refine (tsum_congr ?_).trans (h₁.tsum_add h₂)
  intro x
  have h := Set.indicator_union_of_disjoint hdisj (f := f)
  rw [hunion] at h
  exact congrFun h x

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
  classical
  have hfin : ({ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T}).Finite := ZeroCount1623.stripZeros_finite χ T
  haveI : Finite {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T} := hfin.to_subtype
  refine tsum_indicator_split_quarter
    (s₁ := {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T} | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(13 / 8) ∧ |ρ.val.im| ≤ 2})
    (s₂ := {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T} | -(13 / 8) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2})
    (s := {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T} | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2})
    (f := fun ρ => mellinMassTerm χ δ ρ.val) ?_ ?_
  · rw [Set.disjoint_left]
    intro x hx hy
    simp only [Set.mem_setOf_eq] at hx hy
    linarith [hx.2.1, hy.1]
  · ext x
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, by linarith, h3⟩
      · exact ⟨by linarith, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      by_cases h4 : x.val.im ≤ -(13 / 8)
      · exact Or.inl ⟨h1, h4, h3⟩
      · exact Or.inr ⟨by linarith, h2, h3⟩

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
