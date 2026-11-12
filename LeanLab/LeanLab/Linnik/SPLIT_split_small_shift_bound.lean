/-
OFF ROUTE, architect 20261112T0802Z-24456 U-1647, 2026-11-12. Do not spend prover time here.
This file re-cuts `Display5PlainExpansion`, the C = 0 form whose leaf
`Decomp1532c.display5_plain_expansion` was RETIRED on 2026-11-06 by architect U-1625 as stronger
than the printed source: Gallagher 1975 P0094 Theorem 3 p.127 and display 5 p.138 keep the term
`e^{-c/θ}`, a fixed positive multiple of the main size for fixed θ, and display 6 p.139 absorbs
it only by letting θ tend to zero with k. Both leaves here assert the C = 0 form and are strictly stronger than the source. The live route statement is
`LeanLab.Linnik.Decomp1532c.major_arc_remainder_bound`, which keeps `C * Real.exp (-c / θ)` and
is supplied by `Decomp466c.major_arc_remainder_bound_split` from the cited Theorem 3.
No assembly on the route imports this file. Statements below are unchanged; they are not to be
repaired, since a leaf stronger than the source on a dead branch has no repair worth making.

Split of `LeanLab.Linnik.SPLIT_display5_plain_expansion.split_small_shift_bound`.

The sealed statement bounds the averaged major correlation error over the tuple pairs whose shift
`dif x` is nonzero and no larger than the major arc scale `N ^ θ`. This file cuts that one range
at the half scale `N ^ (θ / 2)` and bounds the two pieces separately. The cut is by the size of
the shift, and the pieces are of different size: an arc of `majorArcs N (N ^ θ)` has half width
`N ^ θ / (q N)`, so the phase `dif x * α` moves by at most about `N ^ (3 θ / 2 - 1)` across an arc
for a shift of the lower piece, and by up to `N ^ (2 θ - 1)` for a shift of the upper piece, a
factor `N ^ (θ / 2)` more. The lower piece is the range where the shift is smallest against the
arc width and the upper piece the range where it is largest, still below the scale. Each piece
carries half of the budget `δ / 3`, and the two bounds add.

Leaves, one per piece at fixed `N`, `θ`, `k`, `δ`:
* `split_small_shift_constant_phase`: `|dif x| ≤ N ^ (θ / 2)`;
* `split_small_shift_oscillating_phase`: `N ^ (θ / 2) < |dif x| ≤ N ^ θ`.

The two ranges are disjoint and cover every tuple of the sealed range, whose own second inequality
`|dif x| ≤ N ^ θ` is repeated in each filter. Assembly: `split_small_shift_bound_split`, the
sealed statement, from the two leaves, with no sorry.

AI-written Lean code, DeepSeek V4.1 Flash Low, 2026-11-11. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.SPLIT_display5_plain_expansion

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- LEAF, OPEN. First piece of the small shift range, the lower one. These are the tuples of the
sealed range with `|dif x| ≤ N ^ (θ / 2)`, where the shift is smallest against the arc width: the
phase `dif x * α` moves by at most about `N ^ (3 θ / 2 - 1)` across an arc of
`majorArcs N (N ^ θ)`. The averaged correlation error with both sums restricted to this piece is
at most a sixth of the budget factor once `N` is large. -/
theorem split_small_shift_constant_phase :
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
  sorry

/-- LEAF, OPEN. Second piece of the small shift range, the upper one. These are the tuples of the
sealed range with `N ^ (θ / 2) < |dif x| ≤ N ^ θ`, where the shift is largest against the arc
width: the phase `dif x * α` moves by up to about `N ^ (2 θ - 1)` across an arc of
`majorArcs N (N ^ θ)`, a factor `N ^ (θ / 2)` more than in the lower piece. The averaged
correlation error with both sums restricted to this piece is at most a sixth of the budget factor
once `N` is large. -/
theorem split_small_shift_oscillating_phase :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 6) := by
  sorry

/-- ASSEMBLY. The sealed statement `split_small_shift_bound`, from the two pieces of the small
shift range: split the tuple sum at `N ^ (θ / 2)`, apply each leaf to its piece, and add the two
bounds, the two sixths of the budget factor giving `δ / 3`. No sorry is used. -/
theorem split_small_shift_bound_split :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 3) := by
  classical
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₁, h₁⟩ := split_small_shift_constant_phase θ hθ hθ4 k hk δ hδ
  obtain ⟨N₂, h₂⟩ := split_small_shift_oscillating_phase θ hθ hθ4 k hk δ hδ
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N := le_trans (le_max_left N₁ N₂) hN
  have hN₂ : N₂ ≤ N := le_trans (le_max_right N₁ N₂) hN
  let T : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :=
    Finset.univ.filter (fun x => LeanLab.Linnik.Decomp1532a.dif x ≠ 0)
  let p1 : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)
  let p2 : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ
  let g : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re
  let w : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
      (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  have E₁ : (T.filter p2).filter p1
      = Finset.univ.filter (fun x =>
          LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧ (p1 x ∧ p2 x)) := by
    simp only [T, Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by tauto)
  have E₂ : (T.filter p2).filter (fun x => ¬ p1 x)
      = Finset.univ.filter (fun x =>
          LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧ (¬ p1 x ∧ p2 x)) := by
    simp only [T, Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by tauto)
  have H₁ : |((T.filter p2).filter p1).sum g - ((T.filter p2).filter p1).sum w| ≤
      M * (δ / 6) := by
    rw [E₁]
    simpa only [p1, p2, g, w, M] using h₁ N hN₁
  have H₂ : |((T.filter p2).filter (fun x => ¬ p1 x)).sum g -
      ((T.filter p2).filter (fun x => ¬ p1 x)).sum w| ≤ M * (δ / 6) := by
    rw [E₂]
    simpa only [p1, p2, g, w, M] using h₂ N hN₂
  have hsplit : ∀ F : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ,
      (T.filter p2).sum F = ((T.filter p2).filter p1).sum F
        + ((T.filter p2).filter (fun x => ¬ p1 x)).sum F :=
    fun F => (Finset.sum_filter_add_sum_filter_not (T.filter p2) p1 F).symm
  have key : |(T.filter p2).sum g - (T.filter p2).sum w| ≤ M * (δ / 3) := by
    have step : (T.filter p2).sum g - (T.filter p2).sum w =
        (((T.filter p2).filter p1).sum g - ((T.filter p2).filter p1).sum w)
          + (((T.filter p2).filter (fun x => ¬ p1 x)).sum g -
              ((T.filter p2).filter (fun x => ¬ p1 x)).sum w) := by
      rw [hsplit g, hsplit w]
      ring
    rw [step]
    have t1 := abs_add_le
      (((T.filter p2).filter p1).sum g - ((T.filter p2).filter p1).sum w)
      (((T.filter p2).filter (fun x => ¬ p1 x)).sum g -
        ((T.filter p2).filter (fun x => ¬ p1 x)).sum w)
    linarith [t1, H₁, H₂]
  simpa only [T, p2, g, w, M, Finset.filter_filter] using key
