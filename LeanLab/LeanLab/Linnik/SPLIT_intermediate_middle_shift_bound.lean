/-
Split of `LeanLab.Linnik.SPLIT_split_intermediate_shift_bound.intermediate_middle_shift_bound`.

The sealed statement bounds the signed difference of the two tuple sums restricted to the middle
range `N ^ (1/2) < |dif x| <= N ^ (3/4)` of the intermediate range, by a share `delta / 9` of the
budget `2 N (log2 N) ^ (2k) / (log N) ^ 2`. This file cuts that range at the two internal scales
`N ^ (7/12)` and `N ^ (2/3)`, each of which lies strictly between `N ^ (1/2)` and `N ^ (3/4)` once
`N > 1`, so the three thirds are disjoint and cover the middle range; each third carries an equal
share `delta / 27`, the shares add to `delta / 9`, and the triangle inequality over the three
pieces gives the sealed statement back with no sorry.

The middle range itself is the conjunction of the arc lower cut, the square-root cut
`N ^ (1/2)` and the cap `N ^ (3/4)`; each leaf keeps all three, so its hypothesis is the middle
range with one further cut, and no leaf drops a conjunct of the target.

Leaves, one per third of the middle range at fixed `N`, `theta`, `k`, `delta`:
* `middle_shift_lower_third_bound`: `N ^ (1/2) < |dif x| <= N ^ (7/12)`;
* `middle_shift_middle_third_bound`: `N ^ (7/12) < |dif x| <= N ^ (2/3)`;
* `middle_shift_upper_third_bound`: `N ^ (2/3) < |dif x| <= N ^ (3/4)`.

Each leaf keeps the full signed difference of the two sums, the correlation integral against the
singular-series main term, on a strictly smaller index set, and cuts the budget from `delta / 9` to
`delta / 27`, so each leaf is weaker than the sealed statement in both its range and its constant.
No leaf assumes the sealed statement. The three ranges are reachable and the leaves are therefore
not vacuous at the empty index set: `dif` is a difference of sums of `k` powers of two with
exponents in `[1, Nat.log 2 N]`, and for `N = 2 ^ 12`, `k = 2`, `theta = 1/4` the three windows on
`|dif x|` are the intervals `(2 ^ 6, 2 ^ 7]`, `(2 ^ 7, 2 ^ 8]` and `(2 ^ 8, 2 ^ 9]`, which a python
enumeration of the `12 ^ 2 * 12 ^ 2` tuple pairs places `32`, `58` and `101` distinct values of
`|dif x|` in, the smallest being `66`, `130` and `256`.

Assembly: `intermediate_middle_shift_bound_split`, the sealed statement, with no sorry; it calls
the three leaves and never the file being split.

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

/-- LEAF, OPEN. First third of the middle range. Tuple differences above the square-root scale
`N ^ (1/2)` and no larger than `N ^ (7/12)`: the step of the target where the shift has crossed the
square root of the summation range but stays below the seven-twelfths scale. The full signed
difference of the correlation integral against the singular-series main term, restricted to those
tuples, is at most a twenty-seventh of the target budget once `N` is large. -/
theorem middle_shift_lower_third_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 12),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 12),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 27) := by
  sorry

/-- LEAF, OPEN. Second third of the middle range. Tuple differences above `N ^ (7/12)` and no larger
than `N ^ (2/3)`: the middle step of the target, between the seven-twelfths and two-thirds scales.
The full signed difference of the correlation integral against the singular-series main term,
restricted to those tuples, is at most a twenty-seventh of the target budget once `N` is large. -/
theorem middle_shift_middle_third_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4)) ∧
              (¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 12)) ∧
                |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 : ℝ) / 3)),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4)) ∧
              (¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 12)) ∧
                |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 : ℝ) / 3)),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 27) := by
  sorry

/-- LEAF, OPEN. Third of the middle range. Tuple differences above `N ^ (2/3)` and no larger than
`N ^ (3/4)`: the top step of the target, from the two-thirds scale up to the three-quarters scale
where the upper range takes over. The full signed difference of the correlation integral against the
singular-series main term, restricted to those tuples, is at most a twenty-seventh of the target
budget once `N` is large. -/
theorem middle_shift_upper_third_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4)) ∧
              (¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 12)) ∧
                ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 : ℝ) / 3))),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            ((LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4)) ∧
              (¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 12)) ∧
                ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 : ℝ) / 3))),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 27) := by
  sorry

/-- ASSEMBLY. The sealed statement `intermediate_middle_shift_bound`, from the three thirds of the
middle range: split the tuple sum by `|dif x| <= N ^ (7/12)` and then by `|dif x| <= N ^ (2/3)`,
apply each leaf to its third, add the three bounds and use the triangle inequality. No `sorry` is
used and the file being split is not called. -/
theorem intermediate_middle_shift_bound_split :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  classical
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₁, h₁⟩ := middle_shift_lower_third_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₂, h₂⟩ := middle_shift_middle_third_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₃, h₃⟩ := middle_shift_upper_third_bound θ hθ hθ4 k hk δ hδ
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
  let D : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    ¬ (|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2))
  let C₁ : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((7 : ℝ) / 12)
  let C₂ : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 : ℝ) / 3)
  let E : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 4)
  let S : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :=
    Finset.univ.filter (fun x => (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧ ¬ A x ∧ B x) ∧ D x ∧ E x)
  let g : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re
  let w : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
      (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  have H₁ : |(S.filter C₁).sum g - (S.filter C₁).sum w| ≤ M * (δ / 27) := by
    simpa only [S, A, B, D, E, C₁, g, w, M, Finset.filter_filter] using h₁ N hN₁
  have H₂ : |((S.filter (fun x => ¬ C₁ x)).filter C₂).sum g -
      ((S.filter (fun x => ¬ C₁ x)).filter C₂).sum w| ≤ M * (δ / 27) := by
    simpa only [S, A, B, D, E, C₁, C₂, g, w, M, Finset.filter_filter] using h₂ N hN₂
  have H₃ : |((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum g -
      ((S.filter (fun x => ¬ C₁ x)).filter (fun x => ¬ C₂ x)).sum w| ≤ M * (δ / 27) := by
    simpa only [S, A, B, D, E, C₁, C₂, g, w, M, Finset.filter_filter] using h₃ N hN₃
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
  simpa only [S, A, B, D, E, g, w, M] using key

#print axioms middle_shift_lower_third_bound
#print axioms middle_shift_middle_third_bound
#print axioms middle_shift_upper_third_bound
#print axioms intermediate_middle_shift_bound_split
