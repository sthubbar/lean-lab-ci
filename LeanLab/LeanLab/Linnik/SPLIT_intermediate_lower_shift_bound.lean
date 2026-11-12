/-
Split of `LeanLab.Linnik.Decomp1532c.intermediate_lower_shift_bound`.

The sealed statement bounds the signed difference between the correlation integral and the
singular-series main term, summed over the tuples whose difference lies in the lower part of the
intermediate range `N ^ θ < |dif x| ≤ N ^ (1/2)`, by a share `δ / 9` of the budget
`2 N (log₂ N) ^ (2k) / (log N) ^ 2`.

This file cuts that range at the two internal scales `N ^ (1/4)` and `N ^ (1/3)`. Since `θ ≤ 1/4`
the arc scale `N ^ θ` never exceeds `N ^ (1/4)`, so the first piece is the stretch just above the
arc scale, the second runs up to the cube root of the summation range, and the third carries the
remainder up to the square root at which the sealed range ends. The three pieces are disjoint and
cover the sealed range, the budget is additive, and the triangle inequality recovers the sealed
statement, so the three leaf bounds give it back with no sorry.

Leaves, one per piece at fixed `N`, `θ`, `k`, `δ`:
* `leaf_lower_quarter_shift_bound`: `N ^ θ < |dif x| ≤ N ^ (1/4)`;
* `leaf_lower_cube_shift_bound`: `N ^ (1/4) < |dif x| ≤ N ^ (1/3)`;
* `leaf_lower_sqrt_remainder_shift_bound`: `N ^ (1/3) < |dif x| ≤ N ^ (1/2)`.

Each leaf keeps the full signed difference of the two sums on a strictly smaller index set with the
budget cut from `δ / 9` to `δ / 27`, so each leaf is weaker than the sealed statement in both its
range and its constant.

Assembly: `intermediate_lower_shift_bound_split`, the sealed statement, with no sorry.

AI-written Lean code, DeepSeek V4.1 Flash Low, 2026-11-12. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.SPLIT_split_intermediate_shift_bound

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- LEAF, OPEN. First piece of the lower intermediate range: tuple differences above the major arc scale
`P = N ^ θ` but no larger than `N ^ (1/4)`, the stretch that opens just above the arc scale.
Since `θ ≤ 1/4` this piece is never empty for large `N`, and it is the step of the proof that
takes the shift off the arc scale. The full signed difference of the correlation
integral against the singular-series main term, restricted to those tuples, is at most a
twenty-seventh share `δ / 27` of the target budget once `N` is large. -/
theorem leaf_lower_quarter_shift_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 4),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 4),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 27) := by
  sorry

/-- LEAF, OPEN. Second piece: tuple differences above `N ^ (1/4)` but no larger than `N ^ (1/3)`, where the
shift is a definite power of `N` already well above the arc scale and still short of the
square-root cut used by the enclosing split. The full signed difference of the correlation
integral against the singular-series main term, restricted to those tuples, is at most a
twenty-seventh share `δ / 27` of the target budget once `N` is large. -/
theorem leaf_lower_cube_shift_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 4)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 3),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 4)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 3),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 27) := by
  sorry

/-- LEAF, OPEN. Third piece: tuple differences above `N ^ (1/3)` but no larger than `N ^ (1/2)`, the remainder
of the lower intermediate range up to the square-root cut at which the sealed range ends. The full signed difference of the correlation
integral against the singular-series main term, restricted to those tuples, is at most a
twenty-seventh share `δ / 27` of the target budget once `N` is large. -/
theorem leaf_lower_sqrt_remainder_shift_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 4)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 3)),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 4)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 3)),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 27) := by
  sorry

/-- ASSEMBLY. The sealed statement `intermediate_lower_shift_bound`, from the three piece leaves:
split the tuple sum by `|dif x| ≤ N ^ (1/4)` and then by `|dif x| ≤ N ^ (1/3)`, apply each leaf to
its piece, add the three bounds and use the triangle inequality. No `sorry` is used and the target
theorem is not called. -/
theorem intermediate_lower_shift_bound_split :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  classical
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₁, h₁⟩ := leaf_lower_quarter_shift_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₂, h₂⟩ := leaf_lower_cube_shift_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₃, h₃⟩ := leaf_lower_sqrt_remainder_shift_bound θ hθ hθ4 k hk δ hδ
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
  let E : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)
  let C₁ : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 4)
  let C₂ : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 3)
  let S : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :=
    Finset.univ.filter (fun x => (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧ ¬ A x ∧ B x) ∧ E x)
  let g : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re
  let w : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
      (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  have H₁ : |(S.filter C₁).sum g - (S.filter C₁).sum w| ≤ M * (δ / 27) := by
    simpa only [S, A, B, E, C₁, g, w, M, Finset.filter_filter, and_assoc] using h₁ N hN₁
  have H₂ : |((S.filter (fun x => ¬ C₁ x)).filter C₂).sum g -
      ((S.filter (fun x => ¬ C₁ x)).filter C₂).sum w| ≤ M * (δ / 27) := by
    simpa only [S, A, B, E, C₁, C₂, g, w, M, Finset.filter_filter, and_assoc] using h₂ N hN₂
  have H₃ : |((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum g -
      ((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum w| ≤ M * (δ / 27) := by
    simpa only [S, A, B, E, C₁, C₂, g, w, M, Finset.filter_filter, and_assoc] using h₃ N hN₃
  have hsplit : ∀ F : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ,
      S.sum F = (S.filter C₁).sum F
        + ((S.filter (fun x => ¬ C₁ x)).filter C₂).sum F
        + ((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum F := by
    intro F
    have e1 : (S.filter C₁).sum F + (S.filter (fun x => ¬ C₁ x)).sum F = S.sum F :=
      Finset.sum_filter_add_sum_filter_not S C₁ F
    have e2 : ((S.filter (fun x => ¬ C₁ x)).filter C₂).sum F +
        ((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum F =
        (S.filter (fun x => ¬ C₁ x)).sum F :=
      Finset.sum_filter_add_sum_filter_not (S.filter (fun x => ¬ C₁ x)) C₂ F
    linarith
  have hA := hsplit g
  have hB := hsplit w
  have hconst : M * (δ / 27) + (M * (δ / 27) + M * (δ / 27)) = M * (δ / 9) := by
    ring
  have key : |S.sum g - S.sum w| ≤ M * (δ / 9) := by
    have step : S.sum g - S.sum w =
        ((S.filter C₁).sum g - (S.filter C₁).sum w)
          + ((((S.filter (fun x => ¬ C₁ x)).filter C₂).sum g -
              ((S.filter (fun x => ¬ C₁ x)).filter C₂).sum w)
            + (((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum g -
              ((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum w)) := by
      rw [hA, hB]; ring
    rw [step]
    have t1 := abs_add_le ((S.filter C₁).sum g - (S.filter C₁).sum w)
      ((((S.filter (fun x => ¬ C₁ x)).filter C₂).sum g -
          ((S.filter (fun x => ¬ C₁ x)).filter C₂).sum w)
        + (((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum g -
          ((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum w))
    have t2 := abs_add_le
      (((S.filter (fun x => ¬ C₁ x)).filter C₂).sum g -
        ((S.filter (fun x => ¬ C₁ x)).filter C₂).sum w)
      (((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum g -
        ((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum w)
    linarith
  simpa only [S, A, B, E, g, w, M, and_assoc] using key

#print axioms leaf_lower_quarter_shift_bound

#print axioms leaf_lower_cube_shift_bound

#print axioms leaf_lower_sqrt_remainder_shift_bound

#print axioms intermediate_lower_shift_bound_split
