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
budget cut from `δ / 9` to `δ / 27`. Neither restricting a signed sum nor decreasing its budget
follows from the enclosing bound. The leaves require their own analytic estimates.

Assembly: `intermediate_lower_shift_bound_split`, the sealed statement, with no sorry.

AI-written Lean code, DeepSeek V4.1 Flash Low, 2026-11-12. Checked only by the Lean kernel.
Helper reductions and the empty endpoint branch: GPT-6.1 Sol, FREE-gh-copilot task348.
Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.SPLIT_split_intermediate_shift_bound
import LeanLab.Linnik.LowerShiftBudget

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- Gallagher 1975 p.127 Theorem 3 and p.138 before display 5.
For any finite collection of tuple pairs, its signed correlation error is at most
the sum of the complex frequency errors on that same collection.
This reduction does not assert that the frequency errors vanish.
AI wrote the Lean code. Binary Goldbach is open. -/
theorem lower_shift_error_le_complex_sum (k L N : ℕ) (θ : ℝ)
    (s : Finset (LeanLab.Linnik.Decomp1532a.pairs k L)) :
    |(∑ x ∈ s, ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
      (∑ x ∈ s,
        LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
          (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
      ∑ x ∈ s, LeanLab.Linnik.Decomp466a.complexFrequencyError N θ
        (LeanLab.Linnik.Decomp1532a.dif x) := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  exact LeanLab.Linnik.Decomp466a.frequencyError_le_complexFrequencyError N θ _

/-- Gallagher 1975 p.127 Theorem 3 and p.138 before display 5.
An eventual bound for the sum of complex errors on a chosen family of finite
collections implies the same eventual bound for their signed correlation errors.
CONDITIONAL ON the supplied bound for the complex errors.
AI wrote the Lean code. Binary Goldbach is open. -/
theorem lower_shift_eventual_bound_of_complex_sum (k : ℕ) (θ : ℝ)
    (s : (N : ℕ) → Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)))
    (B : ℕ → ℝ)
    (h : ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
      (∑ x ∈ s N, LeanLab.Linnik.Decomp466a.complexFrequencyError N θ
        (LeanLab.Linnik.Decomp1532a.dif x)) ≤ B N) :
    ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
      |(∑ x ∈ s N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
          ‖Sg N α‖ ^ 2 *
            (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
        (∑ x ∈ s N,
          LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
            (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
        B N := by
  obtain ⟨Nk, hNk⟩ := h
  exact ⟨Nk, fun N hN =>
    (lower_shift_error_le_complex_sum k (Nat.log 2 N) N θ (s N)).trans (hNk N hN)⟩

/-- LEAF, OPEN. First piece of the lower intermediate range: tuple differences above the major arc scale
`P = N ^ θ` but no larger than `N ^ (1/4)`, the stretch that opens just above the arc scale.
At `θ = 1/4` this piece is empty. Below that endpoint it is the step of the proof that
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
  classical
  intro θ hθ hθ4 k hk δ hδ
  by_cases hθeq : θ = 1 / 4
  · subst θ
    refine ⟨0, fun N _ => ?_⟩
    have hempty :
        (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
          (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
            ¬ (|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 4)) ∧
            |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)) ∧
            |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 2) ∧
            |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 : ℝ) / 4))) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x _
      exact fun hx => hx.1.2.1 hx.2.2
    simp only [hempty, Finset.sum_empty, sub_self, abs_zero]
    positivity
  · apply lower_shift_eventual_bound_of_complex_sum k θ
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
  classical
  intro θ hθ hθ4 k hk δ hδ
  apply lower_shift_eventual_bound_of_complex_sum k θ
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
  classical
  intro θ hθ hθ4 k hk δ hδ
  apply lower_shift_eventual_bound_of_complex_sum k θ
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

#print axioms lower_shift_error_le_complex_sum

#print axioms lower_shift_eventual_bound_of_complex_sum

#print axioms lower_shift_fixed_exponential_budget_obstruction

#print axioms leaf_lower_quarter_shift_bound

#print axioms leaf_lower_cube_shift_bound

#print axioms leaf_lower_sqrt_remainder_shift_bound

#print axioms intermediate_lower_shift_bound_split
