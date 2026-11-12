/-
Split of `LeanLab.Linnik.Decomp1532c.split_small_shift_oscillating_phase`.

The sealed statement is the upper piece of the small shift range of
`SPLIT_split_small_shift_bound`: the tuples of `pairs k (log 2 N)` whose shift `dif x` is nonzero,
larger than `N ^ (θ / 2)` in absolute value and at most `N ^ θ`, with the averaged difference
between the major arc correlation integral and its singular series main term bounded by a sixth of
the budget factor `2 * N * (log 2 N) ^ (2 * k) / (log N) ^ 2`.

This file cuts the upper piece again by the size of the shift, at the intermediate scale
`N ^ (3 * θ / 4)`. An arc of `majorArcs N (N ^ θ)` has half width `N ^ θ / (q * N)`, so the phase
`dif x * α` moves across an arc by at most a constant multiple of `N ^ (5 * θ / 4 - 1)` for a shift
of the lower band and by up to a constant multiple of `N ^ (2 * θ - 1)` for a shift of the upper
band, a factor `N ^ (θ / 4)` more. The two bands are handled separately, each carrying a twelfth of
the budget factor; the two bounds add to the sixth.

Leaves, one per band, at fixed `N`, `θ`, `k`, `δ`:
* `small_shift_oscillating_mid_band`: `N ^ (θ / 2) < |dif x| ≤ N ^ (3 * θ / 4)`;
* `small_shift_oscillating_top_band`: `N ^ (3 * θ / 4) < |dif x| ≤ N ^ θ`.

The two bands are disjoint and cover every tuple of the sealed range; each leaf also repeats the
sealed inequality `|dif x| ≤ N ^ θ` in its own filter, so the two filtered sets are literally the
two halves of the sealed filtered set and no comparison between the two scales is needed.
Assembly: `split_small_shift_oscillating_phase_split`, the sealed statement, from the two leaves,
with no sorry.

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

/-- LEAF, OPEN. Lower band of the oscillating phase range. These are the tuples of the sealed range
whose shift lies in `N ^ (θ / 2) < |dif x| ≤ N ^ (3 * θ / 4)`, where the shift is small enough
against the arc width `N ^ θ / (q * N)` that the phase `dif x * α` moves by at most a constant
multiple of `N ^ (5 * θ / 4 - 1)` across an arc. The averaged correlation error with both sums
restricted to this band is at most a twelfth of the budget factor once `N` is large. -/
theorem small_shift_oscillating_mid_band :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 4) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 4) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 12) := by
  sorry

/-- LEAF, OPEN. Upper band of the oscillating phase range. These are the tuples of the sealed range
whose shift lies in `N ^ (3 * θ / 4) < |dif x| ≤ N ^ θ`, where the shift is largest against the arc
width and the phase `dif x * α` moves by up to a constant multiple of `N ^ (2 * θ - 1)` across an
arc, a factor `N ^ (θ / 4)` more than in the lower band. The averaged correlation error with both
sums restricted to this band is at most a twelfth of the budget factor once `N` is large. -/
theorem small_shift_oscillating_top_band :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 4)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 4)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 12) := by
  sorry

/-- ASSEMBLY. The sealed statement `split_small_shift_oscillating_phase`, from the two bands of the
upper small shift range: split the tuple sum at `N ^ (3 * θ / 4)`, apply each leaf to its band, and
add the two bounds, the two twelfths of the budget factor giving `δ / 6`. No sorry is used. -/
theorem split_small_shift_oscillating_phase_split :
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
  classical
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₁, h₁⟩ := small_shift_oscillating_mid_band θ hθ hθ4 k hk δ hδ
  obtain ⟨N₂, h₂⟩ := small_shift_oscillating_top_band θ hθ hθ4 k hk δ hδ
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N := le_trans (le_max_left N₁ N₂) hN
  have hN₂ : N₂ ≤ N := le_trans (le_max_right N₁ N₂) hN
  let T : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :=
    Finset.univ.filter (fun x => LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
      ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)) ∧
      |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ)
  let q : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 4)
  let g : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re
  let w : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
      (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  have E₁ : T.filter q
      = Finset.univ.filter (fun x =>
          LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
            ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)) ∧
            q x ∧ |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) := by
    simp only [T, Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by tauto)
  have E₂ : T.filter (fun x => ¬ q x)
      = Finset.univ.filter (fun x =>
          LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
            ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)) ∧
            ¬ q x ∧ |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) := by
    simp only [T, Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by tauto)
  have H₁ : |(T.filter q).sum g - (T.filter q).sum w| ≤ M * (δ / 12) := by
    rw [E₁]
    simpa only [q, g, w, M] using h₁ N hN₁
  have H₂ : |(T.filter (fun x => ¬ q x)).sum g - (T.filter (fun x => ¬ q x)).sum w| ≤
      M * (δ / 12) := by
    rw [E₂]
    simpa only [q, g, w, M] using h₂ N hN₂
  have hsplit : ∀ F : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ,
      T.sum F = (T.filter q).sum F + (T.filter (fun x => ¬ q x)).sum F :=
    fun F => (Finset.sum_filter_add_sum_filter_not T q F).symm
  have key : |T.sum g - T.sum w| ≤ M * (δ / 6) := by
    have step : T.sum g - T.sum w =
        ((T.filter q).sum g - (T.filter q).sum w)
          + ((T.filter (fun x => ¬ q x)).sum g - (T.filter (fun x => ¬ q x)).sum w) := by
      rw [hsplit g, hsplit w]
      ring
    rw [step]
    have t1 := abs_add_le
      ((T.filter q).sum g - (T.filter q).sum w)
      ((T.filter (fun x => ¬ q x)).sum g - (T.filter (fun x => ¬ q x)).sum w)
    linarith [t1, H₁, H₂]
  simpa only [T, g, w, M, Finset.filter_filter] using key

#print axioms split_small_shift_oscillating_phase_split
