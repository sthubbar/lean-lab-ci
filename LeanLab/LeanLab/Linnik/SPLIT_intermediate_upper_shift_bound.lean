/-
Split of `LeanLab.Linnik.Decomp1532c.intermediate_upper_shift_bound`.

The sealed statement bounds the signed difference of the two tuple sums restricted to
`N ^ (3/4) < |dif x| ≤ N`, by `δ / 9` of the budget `2 N (log₂ N) ^ (2k) / (log N) ^ 2`. This
file cuts that range again at the two finer scales `N ^ (7/8)` and `N ^ (15/16)`, each sub-range
carrying `δ / 27` of the same budget. The three sub-ranges are disjoint and cover the upper range,
the budget is additive, and the triangle inequality recovers the sealed statement, so the three
leaf bounds give it back with no sorry.

Leaves, one per sub-range of `dif x` at fixed `N`, `θ`, `k`, `δ`:
* `intermediate_upper_low_part_bound`: `N ^ (3/4) < |dif x| ≤ N ^ (7/8)`;
* `intermediate_upper_middle_part_bound`: `N ^ (7/8) < |dif x| ≤ N ^ (15/16)`;
* `intermediate_upper_top_part_bound`: `N ^ (15/16) < |dif x| ≤ N`.

Each leaf keeps the full signed difference of the correlation integral against the
singular-series main term on a strictly smaller index set, with the budget cut from `δ / 9` to
`δ / 27`, so each leaf is weaker than the sealed statement in both its range and its constant.

Assembly: `intermediate_upper_shift_bound_split`, the sealed statement, with no sorry.
-/
import LeanLab.Linnik.SPLIT_split_intermediate_shift_bound

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- LEAF, OPEN. Lowest sub-range of the upper range. Tuple differences above `N ^ (3/4)` but no
larger than `N ^ (7/8)`: the step of the target where the shift has left the `N ^ (3/4)` scale but
stays below the `N ^ (7/8)` scale. The full signed difference of the correlation integral against
the singular-series main term, restricted to those tuples, is at most a twenty-seventh of the
target budget once `N` is large. -/
theorem intermediate_upper_low_part_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4))) ∧ |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 8),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4))) ∧ |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 8),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 27) := by
  sorry

/-- LEAF, OPEN. Middle sub-range of the upper range. Tuple differences above `N ^ (7/8)` but no
larger than `N ^ (15/16)`: the step of the target between the two finer scales, still a positive
power of `N` below the summation range. The full signed difference of the correlation integral
against the singular-series main term, restricted to those tuples, is at most a twenty-seventh of
the target budget once `N` is large. -/
theorem intermediate_upper_middle_part_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4))) ∧ ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 8)) ∧ |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((15 : ℝ) / 16),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4))) ∧ ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 8)) ∧ |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((15 : ℝ) / 16),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 27) := by
  sorry

/-- LEAF, OPEN. Top sub-range of the upper range. Tuple differences above `N ^ (15/16)` but no
larger than `N`: the step of the target where the shift is within a vanishing power of the
summation range itself. The full signed difference of the correlation integral against the
singular-series main term, restricted to those tuples, is at most a twenty-seventh of the target
budget once `N` is large. -/
theorem intermediate_upper_top_part_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4))) ∧ ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 8)) ∧ ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((15 : ℝ) / 16)),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4))) ∧ ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 8)) ∧ ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((15 : ℝ) / 16)),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 27) := by
  sorry

/-- ASSEMBLY. The sealed statement `intermediate_upper_shift_bound`, from the three sub-range
leaves: split the tuple sum by `|dif x| ≤ N ^ (7/8)` and then by `|dif x| ≤ N ^ (15/16)`, apply
each leaf to its sub-range, add the three bounds and use the triangle inequality. No `sorry` is
used and the target theorem is not called. -/
theorem intermediate_upper_shift_bound_split :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4)),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4)),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  classical
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₁, h₁⟩ := intermediate_upper_low_part_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₂, h₂⟩ := intermediate_upper_middle_part_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₃, h₃⟩ := intermediate_upper_top_part_bound θ hθ hθ4 k hk δ hδ
  refine ⟨max (max N₁ N₂) N₃, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N :=
    le_trans (le_trans (le_max_left N₁ N₂) (le_max_left (max N₁ N₂) N₃)) hN
  have hN₂ : N₂ ≤ N :=
    le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) N₃)) hN
  have hN₃ : N₃ ≤ N := le_trans (le_max_right (max N₁ N₂) N₃) hN
  let A : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ
  let B : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)
  let C₁ : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)
  let C₂ : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4)
  let D : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 8)
  let E : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((15 : ℝ) / 16)
  let S : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :=
    Finset.univ.filter (fun x => (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧ ¬ A x ∧ B x) ∧
      ¬ C₁ x ∧ ¬ C₂ x)
  let g : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re
  let w : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
      (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  have H₁ : |(S.filter D).sum g - (S.filter D).sum w| ≤ M * (δ / 27) := by
    simpa only [S, A, B, C₁, C₂, D, g, w, M, Finset.filter_filter] using h₁ N hN₁
  have H₂ : |((S.filter (fun x => ¬ D x)).filter E).sum g -
      ((S.filter (fun x => ¬ D x)).filter E).sum w| ≤ M * (δ / 27) := by
    simpa only [S, A, B, C₁, C₂, D, E, g, w, M, Finset.filter_filter] using h₂ N hN₂
  have H₃ : |((S.filter (fun x => ¬ D x)).filter (fun x => ¬ E x)).sum g -
      ((S.filter (fun x => ¬ D x)).filter (fun x => ¬ E x)).sum w| ≤ M * (δ / 27) := by
    simpa only [S, A, B, C₁, C₂, D, E, g, w, M, Finset.filter_filter] using h₃ N hN₃
  have hsplit : ∀ F : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ,
      S.sum F = (S.filter D).sum F
        + ((S.filter (fun x => ¬ D x)).filter E).sum F
        + ((S.filter (fun x => ¬ D x)).filter (fun x => ¬ E x)).sum F := by
    intro F
    have e1 : (S.filter D).sum F + (S.filter (fun x => ¬ D x)).sum F = S.sum F :=
      Finset.sum_filter_add_sum_filter_not S D F
    have e2 : ((S.filter (fun x => ¬ D x)).filter E).sum F +
        ((S.filter (fun x => ¬ D x)).filter (fun x => ¬ E x)).sum F =
        (S.filter (fun x => ¬ D x)).sum F :=
      Finset.sum_filter_add_sum_filter_not (S.filter (fun x => ¬ D x)) E F
    linarith
  have hA := hsplit g
  have hB := hsplit w
  have hconst : M * (δ / 27) + (M * (δ / 27) + M * (δ / 27)) = M * (δ / 9) := by
    ring
  have key : |S.sum g - S.sum w| ≤ M * (δ / 9) := by
    have step : S.sum g - S.sum w =
        ((S.filter D).sum g - (S.filter D).sum w)
          + ((((S.filter (fun x => ¬ D x)).filter E).sum g -
              ((S.filter (fun x => ¬ D x)).filter E).sum w)
            + (((S.filter (fun x => ¬ D x)).filter (fun x => ¬ E x)).sum g -
              ((S.filter (fun x => ¬ D x)).filter (fun x => ¬ E x)).sum w)) := by
      rw [hA, hB]; ring
    rw [step]
    have t1 := abs_add_le ((S.filter D).sum g - (S.filter D).sum w)
      ((((S.filter (fun x => ¬ D x)).filter E).sum g -
          ((S.filter (fun x => ¬ D x)).filter E).sum w)
        + (((S.filter (fun x => ¬ D x)).filter (fun x => ¬ E x)).sum g -
          ((S.filter (fun x => ¬ D x)).filter (fun x => ¬ E x)).sum w))
    have t2 := abs_add_le
      (((S.filter (fun x => ¬ D x)).filter E).sum g -
        ((S.filter (fun x => ¬ D x)).filter E).sum w)
      (((S.filter (fun x => ¬ D x)).filter (fun x => ¬ E x)).sum g -
        ((S.filter (fun x => ¬ D x)).filter (fun x => ¬ E x)).sum w)
    linarith
  simpa only [S, A, B, C₁, C₂, g, w, M] using key

#print axioms intermediate_upper_shift_bound_split
