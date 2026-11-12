/-
Split of `LeanLab.Linnik.Decomp1532c.large_shift_minor_sum_bound`.

The sealed estimate bounds the total over the long shifts (nonzero tuple difference, absolute value
above `N`) of the correlation of the squared exponential sum with the phase of that shift, taken over
the complement of the major arcs, by a third of the budget `2 N (log₂ N) ^ (2k) / (log N) ^ 2`.

This file cuts that total sum by the size of the shift, at the two scales `2 N` and `N ^ (3/2)`, and
bounds the three pieces separately, each carrying a ninth of the same budget. The cut is where the
shift stops being comparable with the summation range: below `2 N` the difference of the two
exponents on each side is at most the length of the summation range, so the pair structure of the
squared sum is still the whole range; above `2 N` that difference exceeds it and the coefficient of
the squared sum at that shift has run out, while the phase still moves by a full winding across a
major arc; above `N ^ (3/2)` the shift is beyond any power of `N` that the arc width can follow.

The three ranges are disjoint and cover the sealed range, the budget is additive, and the triangle
inequality recovers the sealed statement, so the three leaf bounds give it back with no sorry.

Leaves, one per range of `dif x` at fixed `N`, `θ`, `k`, `δ`:
* `large_shift_near_sum_bound`: `N < |dif x| ≤ 2 N`;
* `large_shift_middle_sum_bound`: `2 N < |dif x| ≤ N ^ (3/2)`;
* `large_shift_far_sum_bound`: `N ^ (3/2) < |dif x|`.

Each leaf keeps the same single sum over the complement of the major arcs on a strictly smaller
index set and cuts the budget factor from `δ / 3` to `δ / 9`, so each is weaker than the sealed
statement in both its range and its constant.

Assembly: `large_shift_minor_sum_bound_split`, the sealed statement, with no sorry.

AI-written Lean code, DeepSeek V4.1 Flash Low, 2026-11-12. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.SPLIT_split_large_shift_bound

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- LEAF, OPEN. First piece of the long shift range, the near one: shifts above the summation range
`N` but no larger than twice it. This is the step of the target where the difference of the two
exponent sums on the two sides of a pair is still of the order of `N`, so every coefficient of the
squared exponential sum contributes, and only the oscillation of the phase over the complement of
the major arcs can save anything. The total of the correlations over the complement of the major
arcs restricted to these tuples is at most a ninth of the budget factor once `N` is large. -/
theorem large_shift_near_sum_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ),
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  sorry

/-- LEAF, OPEN. Second piece of the long shift range, the middle one: shifts above `2 N` but no
larger than `N ^ (3/2)`. This is the step of the target where the difference of the two exponent
sums is larger than the summation range, so the coefficient of the squared exponential sum at that
shift has already dropped out of the diagonal and the correlation has to come from the oscillation
of the phase alone, while the shift is still small enough that the phase moves by a whole winding
across a major arc. The total of the correlations over the complement of the major arcs restricted
to these tuples is at most a ninth of the budget factor once `N` is large. -/
theorem large_shift_middle_sum_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2),
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  sorry

/-- LEAF, OPEN. Third piece of the long shift range, the far one: shifts above `N ^ (3/2)`. This is
the step of the target where the shift has outgrown every power of `N` below the summation range
itself, so it is far above the scale at which the width of a major arc allows the phase to be held
constant, and the correlation over the complement of the major arcs has to be small by the winding
of the phase on each arc alone. The total of the correlations over the complement of the major arcs
restricted to these tuples is at most a ninth of the budget factor once `N` is large. -/
theorem large_shift_far_sum_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2)),
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  sorry

/-- ASSEMBLY. The sealed statement `large_shift_minor_sum_bound`, from the three pieces of the long
shift range: split the tuple sum by `|dif x| ≤ 2 N` and then by `|dif x| ≤ N ^ (3/2)`, apply each
leaf to its piece, add the three bounds and use the triangle inequality, the three ninths of the
budget factor giving `δ / 3`. No sorry is used and the sealed theorem is not called. -/
theorem large_shift_minor_sum_bound_split :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|,
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 3) := by
  classical
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₁, h₁⟩ := large_shift_near_sum_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₂, h₂⟩ := large_shift_middle_sum_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₃, h₃⟩ := large_shift_far_sum_bound θ hθ hθ4 k hk δ hδ
  refine ⟨max (max N₁ N₂) N₃, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N :=
    le_trans (le_trans (le_max_left N₁ N₂) (le_max_left (max N₁ N₂) N₃)) hN
  have hN₂ : N₂ ≤ N :=
    le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) N₃)) hN
  have hN₃ : N₃ ≤ N := le_trans (le_max_right (max N₁ N₂) N₃) hN
  let A : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)
  let B : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2)
  let S : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :=
    Finset.univ.filter (fun x => LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
      (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|)
  let g : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
      ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  have H₁ : |(S.filter A).sum g| ≤ M * (δ / 9) := by
    simpa only [S, A, g, M, Finset.filter_filter, and_assoc] using h₁ N hN₁
  have H₂ : |((S.filter (fun x => ¬ A x)).filter B).sum g| ≤ M * (δ / 9) := by
    simpa only [S, A, B, g, M, Finset.filter_filter, and_assoc] using h₂ N hN₂
  have H₃ : |((S.filter (fun x => ¬ A x)).filter (fun x => ¬ B x)).sum g| ≤ M * (δ / 9) := by
    simpa only [S, A, B, g, M, Finset.filter_filter, and_assoc] using h₃ N hN₃
  have e₁ : (S.filter A).sum g + (S.filter (fun x => ¬ A x)).sum g = S.sum g :=
    Finset.sum_filter_add_sum_filter_not S A g
  have e₂ : ((S.filter (fun x => ¬ A x)).filter B).sum g +
      ((S.filter (fun x => ¬ A x)).filter (fun x => ¬ B x)).sum g =
      (S.filter (fun x => ¬ A x)).sum g :=
    Finset.sum_filter_add_sum_filter_not (S.filter (fun x => ¬ A x)) B g
  have hthree : M * (δ / 9) + M * (δ / 9) + M * (δ / 9) = M * (δ / 3) := by ring
  have hX : |(S.filter (fun x => ¬ A x)).sum g| ≤ M * (δ / 9) + M * (δ / 9) := by
    rw [← e₂]
    exact le_trans (abs_add_le _ _) (by linarith [H₂, H₃])
  have hY : |S.sum g| ≤ |(S.filter A).sum g| + |(S.filter (fun x => ¬ A x)).sum g| := by
    rw [← e₁]
    exact abs_add_le _ _
  have key : |S.sum g| ≤ M * (δ / 3) := by linarith [hY, H₁, hX, hthree]
  simpa only [S, g, M] using key

#print axioms large_shift_minor_sum_bound_split
