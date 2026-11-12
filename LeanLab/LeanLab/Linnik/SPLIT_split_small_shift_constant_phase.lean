/-
Split of the constant phase piece of the small shift range of
`LeanLab.Linnik.Decomp1532c.split_small_shift_bound`.

The sealed statement bounds, at fixed `θ`, `k`, `N`, the averaged difference between the
major-arc correlation integral and its singular series main term, the sum running over the tuples
whose shift `dif x` is nonzero, at most `N ^ (θ / 2)` and at most `N ^ θ`. This file cuts that
range by the size of the shift into four consecutive pieces, at the thresholds `N ^ (θ / 8)`,
`N ^ (θ / 4)` and `N ^ (3 θ / 8)`, and bounds the difference on each piece separately. The
pieces are graded by how far the phase `dif x * α` travels across one arc of
`majorArcs N (N ^ θ)`, whose half width is `N ^ θ / (q N)`: about `N ^ (9 θ / 8 - 1)` on the
first piece, `N ^ (5 θ / 4 - 1)` on the second, `N ^ (11 θ / 8 - 1)` on the third, and about
`N ^ (3 θ / 2 - 1)` on the fourth, the four pieces together covering the whole range of the sealed
statement. Each piece carries a quarter of the sealed budget `δ / 6`, so the four quarters add
back to it.

Leaves, one per piece, each at fixed `θ`, `k`, `δ` and all `N` past its own threshold:
* `split_small_shift_constant_phase_eighth`: `|dif x| ≤ N ^ (θ / 8)`;
* `split_small_shift_constant_phase_quarter`: `N ^ (θ / 8) < |dif x| ≤ N ^ (θ / 4)`;
* `split_small_shift_constant_phase_three_eighths`:
  `N ^ (θ / 4) < |dif x| ≤ N ^ (3 θ / 8)`;
* `split_small_shift_constant_phase_half`:
  `N ^ (3 θ / 8) < |dif x| ≤ N ^ (θ / 2)`.

The four ranges are pairwise disjoint and cover every tuple of the sealed range, whose own bounds
`|dif x| ≤ N ^ (θ / 2)` and `|dif x| ≤ N ^ θ` are repeated in each filter. Assembly:
`split_small_shift_constant_phase_split`, the sealed statement, from the four leaves, with no
sorry, by splitting the tuple sum three times and applying the triangle inequality.

AI-written Lean code, DeepSeek V4.1 Flash Low, 2026-11-12. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.SPLIT_split_small_shift_bound

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- LEAF, OPEN. First of the four consecutive pieces of the constant phase range, the one where
the shift is smallest: the tuples with `|dif x| ≤ N ^ (θ / 8)`, so that the phase `dif x * α`
travels across at most about `N ^ (9 θ / 8 - 1)` on an arc of `majorArcs N (N ^ θ)`. The averaged
difference between the correlation integral and its singular series main term, with both sums
restricted to this piece, is at most a quarter of the sealed budget factor once `N` is large. -/
theorem split_small_shift_constant_phase_eighth :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 8) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 8) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 24) := by
  sorry

/-- LEAF, OPEN. Second of the four consecutive pieces of the constant phase range: the tuples with
`N ^ (θ / 8) < |dif x| ≤ N ^ (θ / 4)`. The phase `dif x * α` travels across at most about
`N ^ (5 θ / 4 - 1)` on an arc of `majorArcs N (N ^ θ)`. The averaged difference between the
correlation integral and its singular series main term, with both sums restricted to this piece,
is at most a quarter of the sealed budget factor once `N` is large. -/
theorem split_small_shift_constant_phase_quarter :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 8)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 4) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 8)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 4) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 24) := by
  sorry

/-- LEAF, OPEN. Third of the four consecutive pieces of the constant phase range: the tuples with
`N ^ (θ / 4) < |dif x| ≤ N ^ (3 θ / 8)`. The phase `dif x * α` travels across at most about
`N ^ (11 θ / 8 - 1)` on an arc of `majorArcs N (N ^ θ)`. The averaged difference between the
correlation integral and its singular series main term, with both sums restricted to this piece,
is at most a quarter of the sealed budget factor once `N` is large. -/
theorem split_small_shift_constant_phase_three_eighths :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 8)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 4)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 8) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 8)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 4)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 8) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 24) := by
  sorry

/-- LEAF, OPEN. Fourth and last of the four consecutive pieces of the constant phase range, the
one where the shift is largest: the tuples with `N ^ (3 θ / 8) < |dif x| ≤ N ^ (θ / 2)`. The
phase `dif x * α` travels across at most about `N ^ (3 θ / 2 - 1)` on an arc of
`majorArcs N (N ^ θ)`, the largest travel in the range. The averaged difference between the
correlation integral and its singular series main term, with both sums restricted to this piece,
is at most a quarter of the sealed budget factor once `N` is large. -/
theorem split_small_shift_constant_phase_half :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 8)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 4)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 8)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 8)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 4)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 8)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 24) := by
  sorry

/-- ASSEMBLY. The sealed statement of `split_small_shift_constant_phase`, from the four
consecutive pieces of the constant phase range: split the tuple sum at `N ^ (θ / 8)`, then at
`N ^ (θ / 4)`, then at `N ^ (3 θ / 8)`, apply the leaf of each piece to its own piece, and add
the four bounds, the four quarters of the budget factor giving `δ / 6`. No sorry is used. -/
theorem split_small_shift_constant_phase_split :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 6) := by
  classical
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₁, h₁⟩ := split_small_shift_constant_phase_eighth θ hθ hθ4 k hk δ hδ
  obtain ⟨N₂, h₂⟩ := split_small_shift_constant_phase_quarter θ hθ hθ4 k hk δ hδ
  obtain ⟨N₃, h₃⟩ := split_small_shift_constant_phase_three_eighths θ hθ hθ4 k hk δ hδ
  obtain ⟨N₄, h₄⟩ := split_small_shift_constant_phase_half θ hθ hθ4 k hk δ hδ
  refine ⟨max (max (max N₁ N₂) N₃) N₄, ?_⟩
  intro N hN
  have e₁ : N₁ ≤ max (max (max N₁ N₂) N₃) N₄ :=
    le_trans (le_max_left N₁ N₂)
      (le_trans (le_max_left (max N₁ N₂) N₃) (le_max_left (max (max N₁ N₂) N₃) N₄))
  have e₂ : N₂ ≤ max (max (max N₁ N₂) N₃) N₄ :=
    le_trans (le_max_right N₁ N₂)
      (le_trans (le_max_left (max N₁ N₂) N₃) (le_max_left (max (max N₁ N₂) N₃) N₄))
  have e₃ : N₃ ≤ max (max (max N₁ N₂) N₃) N₄ :=
    le_trans (le_max_right (max N₁ N₂) N₃) (le_max_left (max (max N₁ N₂) N₃) N₄)
  have e₄ : N₄ ≤ max (max (max N₁ N₂) N₃) N₄ :=
    le_max_right (max (max N₁ N₂) N₃) N₄
  have hN₁ : N₁ ≤ N := le_trans e₁ hN
  have hN₂ : N₂ ≤ N := le_trans e₂ hN
  have hN₃ : N₃ ≤ N := le_trans e₃ hN
  have hN₄ : N₄ ≤ N := le_trans e₄ hN
  let T : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :=
    Finset.univ.filter (fun x => LeanLab.Linnik.Decomp1532a.dif x ≠ 0)
  let p2 : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)
  let p3 : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ
  let q8 : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 8)
  let q4 : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 4)
  let q38 : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 8)
  let S : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) := T.filter (fun x => p2 x ∧ p3 x)
  let g : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re
  let w : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
          (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  let A₁ : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) := S.filter q8
  let B : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) := S.filter (fun x => ¬ q8 x)
  let A₂ : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) := B.filter q4
  let C : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) := B.filter (fun x => ¬ q4 x)
  let A₃ : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) := C.filter q38
  let A₄ : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) := C.filter (fun x => ¬ q38 x)
  have E₁ : A₁ = Finset.univ.filter (fun x =>
      LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧ q8 x ∧ p2 x ∧ p3 x) := by
    simp only [A₁, S, T, Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by tauto)
  have E₂ : A₂ = Finset.univ.filter (fun x =>
      LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧ ¬ q8 x ∧ q4 x ∧ p2 x ∧ p3 x) := by
    simp only [A₂, B, S, T, Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by tauto)
  have E₃ : A₃ = Finset.univ.filter (fun x =>
      LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧ ¬ q8 x ∧ ¬ q4 x ∧ q38 x ∧ p2 x ∧ p3 x) := by
    simp only [A₃, C, B, S, T, Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by tauto)
  have E₄ : A₄ = Finset.univ.filter (fun x =>
      LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧ ¬ q8 x ∧ ¬ q4 x ∧ ¬ q38 x ∧ p2 x ∧ p3 x) := by
    simp only [A₄, C, B, S, T, Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by tauto)
  have H₁ : |A₁.sum g - A₁.sum w| ≤ M * (δ / 24) := by
    rw [E₁]
    simpa only [q8, p2, p3, g, w, M] using h₁ N hN₁
  have H₂ : |A₂.sum g - A₂.sum w| ≤ M * (δ / 24) := by
    rw [E₂]
    simpa only [q8, q4, p2, p3, g, w, M] using h₂ N hN₂
  have H₃ : |A₃.sum g - A₃.sum w| ≤ M * (δ / 24) := by
    rw [E₃]
    simpa only [q8, q4, q38, p2, p3, g, w, M] using h₃ N hN₃
  have H₄ : |A₄.sum g - A₄.sum w| ≤ M * (δ / 24) := by
    rw [E₄]
    simpa only [q8, q4, q38, p2, p3, g, w, M] using h₄ N hN₄
  have s₁g : S.sum g = A₁.sum g + B.sum g :=
    (Finset.sum_filter_add_sum_filter_not S q8 g).symm
  have s₁w : S.sum w = A₁.sum w + B.sum w :=
    (Finset.sum_filter_add_sum_filter_not S q8 w).symm
  have s₂g : B.sum g = A₂.sum g + C.sum g :=
    (Finset.sum_filter_add_sum_filter_not B q4 g).symm
  have s₂w : B.sum w = A₂.sum w + C.sum w :=
    (Finset.sum_filter_add_sum_filter_not B q4 w).symm
  have s₃g : C.sum g = A₃.sum g + A₄.sum g :=
    (Finset.sum_filter_add_sum_filter_not C q38 g).symm
  have s₃w : C.sum w = A₃.sum w + A₄.sum w :=
    (Finset.sum_filter_add_sum_filter_not C q38 w).symm
  have part : S.sum g - S.sum w =
      (A₁.sum g - A₁.sum w) + (A₂.sum g - A₂.sum w)
        + (A₃.sum g - A₃.sum w) + (A₄.sum g - A₄.sum w) := by
    rw [s₁g, s₁w, s₂g, s₂w, s₃g, s₃w]
    ring
  have key : |S.sum g - S.sum w| ≤ M * (δ / 6) := by
    rw [part]
    calc |(A₁.sum g - A₁.sum w) + (A₂.sum g - A₂.sum w)
          + (A₃.sum g - A₃.sum w) + (A₄.sum g - A₄.sum w)|
        = |((A₁.sum g - A₁.sum w) + (A₂.sum g - A₂.sum w))
            + ((A₃.sum g - A₃.sum w) + (A₄.sum g - A₄.sum w))| := by
          congr 1
          ring
      _ ≤ |(A₁.sum g - A₁.sum w) + (A₂.sum g - A₂.sum w)|
            + |(A₃.sum g - A₃.sum w) + (A₄.sum g - A₄.sum w)| :=
          abs_add_le _ _
      _ ≤ (|A₁.sum g - A₁.sum w| + |A₂.sum g - A₂.sum w|)
            + (|A₃.sum g - A₃.sum w| + |A₄.sum g - A₄.sum w|) := by
          have p := abs_add_le (A₁.sum g - A₁.sum w) (A₂.sum g - A₂.sum w)
          have q := abs_add_le (A₃.sum g - A₃.sum w) (A₄.sum g - A₄.sum w)
          linarith
      _ ≤ (M * (δ / 24) + M * (δ / 24)) + (M * (δ / 24) + M * (δ / 24)) := by
          linarith [H₁, H₂, H₃, H₄]
      _ = M * (δ / 6) := by
          ring
  simpa only [S, T, p2, p3, g, w, M, Finset.filter_filter] using key
