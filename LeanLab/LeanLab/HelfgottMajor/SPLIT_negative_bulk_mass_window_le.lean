import LeanLab.HelfgottMajor.SPLIT_negative_bulk_mass_integral

/-!
Split of `negative_bulk_mass_window_le` in
`LeanLab.HelfgottMajor.SPLIT_negative_bulk_mass_integral` into three leaves.

The statement being split bounds the multiplicity weighted Mellin mass attached to the negative
zeros whose ordinate lies between minus two and minus three halves, for a Dirichlet `L`-function in
the strip `0 < re < 1` and below height `T`, by two height integrals over `[1, T]`: the critical
line norms against the mean weight divided by `2 * pi`, and the derivative norms against the
shifted log weight.

The split cuts the ordinate window at minus seven quarters. The window occupies a bounded stretch
of heights, so only boundedly many ordinates lie in it; the parent split pays the whole window out
of the whole mean weight integral together with three quarters of the shifted log weight integral,
and here each of the two halves of the window is paid out of half of each of those budgets. Cutting
a bounded window in two leaves the reason for the bound unchanged on either half, so each half is
strictly easier than the window: it carries less mass against a budget of the same size.

The three right hand sides add up to the bound of the statement being split: one half plus one half
of the mean weight integral, and three eighths plus three eighths of the shifted log weight
integral, which is three quarters of it.

The assembly is the partition identity for the two halves of the window, then the addition of the
two half inequalities, then the arithmetic of the budgets. It has no sorry of its own. All three
leaves are OPEN.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform

/-- The mass of the union of two disjoint sets is the sum of the two masses, for a summand on a
finite index type. Finiteness is what makes every series below summable. -/
private lemma tsum_indicator_split {α : Type*} [Finite α] (s₁ s₂ s : Set α) (f : α → ℝ)
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

/-- LEAF 1 of 3, the partition of the ordinate window at minus seven quarters. The mass over the
closed window from minus two to minus three halves equals the mass over the part of the window at
ordinate at most minus seven quarters plus the mass over the part of the window above minus seven
quarters. The two pieces are disjoint and cover the window, and the mass is finitely supported on
the bounded height range, which is what turns the sum over the union into the sum of the two sums.
This is bookkeeping only: it asserts no bound and no estimate. -/
theorem negative_bulk_mass_window_partition (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) =
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) := by
  classical
  have hfin : ({ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T}).Finite := ZeroCount1623.stripZeros_finite χ T
  haveI : Finite {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T} := hfin.to_subtype
  refine tsum_indicator_split
    (s₁ := {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T} | ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2})
    (s₂ := {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T} | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2})
    (s := {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T} | ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2})
    (f := fun ρ => mellinMassTerm χ δ ρ.val) ?_ ?_
  · rw [Set.disjoint_left]
    intro x hx hy
    simp only [Set.mem_setOf_eq] at hx hy
    linarith [hx.1, hy.1]
  · ext x
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨by linarith, h2⟩
      · exact ⟨h2, h3⟩
    · rintro ⟨h1, h2⟩
      by_cases h3 : x.val.im ≤ -(7 / 4)
      · exact Or.inl ⟨h3, h2⟩
      · exact Or.inr ⟨by linarith, h1, h2⟩

/-- LEAF 2 of 3, the lower half of the window, from minus two to minus seven quarters. The mass
over that half is at most half of the mean weight integral over the height interval plus three
eighths of the shifted log weight integral over the same interval. The half window occupies a
bounded stretch of heights and therefore carries only boundedly many ordinates, so half of each of
the two budgets of the parent split pays for it with room to spare. -/
theorem negative_bulk_mass_lower_window_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
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
  -- Required: an explicit count of the ordinates in a bounded height range together with a
  -- pointwise envelope for the mass on that range, charged against half of each budget.
  sorry

/-- LEAF 3 of 3, the upper half of the window, above minus seven quarters and at most minus three
halves. The mass over that half is at most the other half of the mean weight integral over the
height interval plus the other three eighths of the shifted log weight integral over the same
interval. The piece is adjacent to the reference height of the parent split, and being a bounded
stretch of heights it again carries only boundedly many ordinates, so the remaining halves of the
two budgets pay for it. -/
theorem negative_bulk_mass_upper_window_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
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
  -- Required: the same count and pointwise envelope as the lower half, on the piece of the window
  -- nearest the reference height, charged against the remaining halves of the two budgets.
  sorry

/-- The statement of `negative_bulk_mass_window_le`, assembled from the three leaves: the window
mass splits into the mass of its two halves, each half is bounded by half of the mean weight
integral plus three eighths of the shifted log weight integral, and one half plus one half of the
first budget with three eighths plus three eighths of the second is the budget of the statement. -/
theorem negative_bulk_mass_window_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
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
  have harith : ∀ A B : ℝ,
      ((1 / 2) * A + (3 / 8) * B) + ((1 / 2) * A + (3 / 8) * B) = A + (3 / 4) * B := by
    intro A B
    ring
  have hpart := negative_bulk_mass_window_partition q χ δ T hT
  have hlow := negative_bulk_mass_lower_window_le q χ δ T hT
  have hup := negative_bulk_mass_upper_window_le q χ δ T hT
  calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ)
      = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
          (fun ρ => mellinMassTerm χ δ ρ.val) ρ) := hpart
    _ ≤ ((1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
            ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              log ((q : ℝ) * t / (2 * π)))) +
          (3 / 8) * (∫ t in (1 : ℝ)..T,
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              (0.15 * log ((q : ℝ) * t) + 3.389))) +
        ((1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
            ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              log ((q : ℝ) * t / (2 * π)))) +
          (3 / 8) * (∫ t in (1 : ℝ)..T,
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
              (0.15 * log ((q : ℝ) * t) + 3.389))) := add_le_add hlow hup
    _ = (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
            log ((q : ℝ) * t / (2 * π))) +
        (3 / 4) * (∫ t in (1 : ℝ)..T,
          ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
            (0.15 * log ((q : ℝ) * t) + 3.389)) :=
      harith _ _

end LeanLab.HelfgottMajor.Decomp431a
