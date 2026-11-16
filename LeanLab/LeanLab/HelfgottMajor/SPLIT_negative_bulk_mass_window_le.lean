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
  let S := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
  have hfin : Set.Finite (Set.univ : Set S) := by
    have hstrip_fin : Set.Finite (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros χ T) :=
      LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ T
    have h_sub : (Set.univ : Set S) ⊆
        (fun (ρ : S) => (ρ : ℂ)) ⁻¹' (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros χ T) := by
      intro ρ _
      simp [LeanLab.HelfgottMajor.ZeroCount1623.stripZeros, S, ρ.property]
    exact Set.Finite.subset (hstrip_fin.preimage Subtype.val_injective.injOn) h_sub
  let fs : Finset S := hfin.toFinset
  have hfs : ∀ x, x ∈ fs ↔ True := by
    intro x; simp [fs, hfin.mem_toFinset]
  have h_indicator_split : ∀ (ρ : S),
      Set.indicator ({ρ | ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2} : Set S)
        (fun ρ => mellinMassTerm χ δ ρ.val) ρ =
      Set.indicator ({ρ | ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2} : Set S)
        (fun ρ => mellinMassTerm χ δ ρ.val) ρ +
      Set.indicator ({ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2} : Set S)
        (fun ρ => mellinMassTerm χ δ ρ.val) ρ := by
    intro ρ
    by_cases hmem : ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2
    · rcases hmem with ⟨him_le, hi_abs⟩
      by_cases hsplit : ρ.val.im ≤ -(7 / 4)
      · have h_not_upper : ¬(-(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2) := by
          intro ⟨hlt, _, _⟩; linarith
        simp [Set.indicator_apply, hmem, hsplit, h_not_upper]
      · have h_upper : -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2 := by
          exact ⟨by linarith, him_le, hi_abs⟩
        simp [Set.indicator_apply, hmem, hsplit, h_upper]
    · have h_not_lower : ¬(ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2) := by
        intro ⟨h1, h2⟩; exact hmem ⟨by linarith, h2⟩
      have h_not_upper : ¬(-(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2) := by
        intro ⟨hlt, him_le, hi_abs⟩; exact hmem ⟨him_le, hi_abs⟩
      simp [Set.indicator_apply, hmem, h_not_lower, h_not_upper]
  have h_tsum_eq_finset (f : S → ℝ) : (∑' ρ : S, f ρ) = ∑ ρ in fs, f ρ := by
    apply (hfin.tsum_eq_sum fs).symm
  calc
    (∑' ρ : S, Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
        (fun ρ => mellinMassTerm χ δ ρ.val) ρ)
    = ∑ ρ in fs, Set.indicator {ρ | ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
        (fun ρ => mellinMassTerm χ δ ρ.val) ρ := h_tsum_eq_finset _
    _ = ∑ ρ in fs, (Set.indicator {ρ | ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2}
        (fun ρ => mellinMassTerm χ δ ρ.val) ρ +
        Set.indicator {ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
        (fun ρ => mellinMassTerm χ δ ρ.val) ρ) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      simp [h_indicator_split ρ]
    _ = (∑ ρ in fs, Set.indicator {ρ | ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2}
        (fun ρ => mellinMassTerm χ δ ρ.val) ρ) +
        (∑ ρ in fs, Set.indicator {ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
        (fun ρ => mellinMassTerm χ δ ρ.val) ρ) :=
      Finset.sum_add_distrib
    _ = (∑' ρ : S, Set.indicator {ρ | ρ.val.im ≤ -(7 / 4) ∧ |ρ.val.im| ≤ 2}
        (fun ρ => mellinMassTerm χ δ ρ.val) ρ) +
        (∑' ρ : S, Set.indicator {ρ | -(7 / 4) < ρ.val.im ∧ ρ.val.im ≤ -(3 / 2) ∧ |ρ.val.im| ≤ 2}
        (fun ρ => mellinMassTerm χ δ ρ.val) ρ) := by
      simp [h_tsum_eq_finset]

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
  -- BLOCKED OUT OF REACH 2026-11-16 FREE-ms-leanstral task672 negative_bulk_mass_lower_window_le
  -- Required: factor-2 slack over parent negative_bulk_mass_window_le (BLOCKED OUT OF REACH
  -- 2026-11-14 FREE-ms-leanstral task484). The parent gives L₁ + L₂ ≤ A + (3/4)B, but
  -- negative_bulk_mass_lower_window_le requires L₁ ≤ A/2 + (3/8)B, which does not follow
  -- from the parent. Requires explicit formula with residue and zero counting estimate.
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
  -- BLOCKED OUT OF REACH 2026-11-16 FREE-ms-leanstral task672 negative_bulk_mass_upper_window_le
  -- Required: same factor-2 slack as negative_bulk_mass_lower_window_le.
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
