/-
Split of `LeanLab.Linnik.Decomp1532c.display5_plain_expansion`.

The sealed statement `Display5PlainExpansion` is one eventual bound for the averaged major arc
correlation error: the whole difference of the two tuple sums is bounded by a share `δ` of
`2 N L ^ (2k) / log N ^ 2`. The single open proof step is cut here by the size of the tuple
difference `dif x`. The three ranges are disjoint and cover every tuple with `dif x ≠ 0`, and the
budget `δ` is additive, so the three leaf bounds give the sealed statement back.

Leaves, one per range of `dif x` at fixed `N`, `θ`, `k`, `δ`:
* `split_small_shift_bound`: `|dif x| ≤ N ^ θ`, the shifts no larger than the major arc scale
  `P = N ^ θ`;
* `split_intermediate_shift_bound`: `N ^ θ < |dif x| ≤ N`;
* `split_large_shift_bound`: `N < |dif x|`.

Assembly: `display5_plain_expansion_split`, the sealed statement, with no sorry.

AI-written Lean code, DeepSeek V4.1 Flash Low, 2026-11-07. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.Decomp1532c

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- LEAF, OPEN. First range only. Tuple differences no larger than the major arc scale
`P = N ^ θ`, so `|dif x| ≤ N ^ θ`. The averaged correlation error with both sums restricted to
those tuples is at most a third of the target budget once `N` is large. This is one step of the
target: it is the part of the signed difference carried by the short shifts, with the full tuple
average still in place. -/
theorem split_small_shift_bound :
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
  sorry

/-- LEAF, OPEN. Second range only. Tuple differences above the major arc scale but no larger than
`N`: `N ^ θ < |dif x| ≤ N`. The averaged correlation error with both sums restricted to those
tuples is at most a third of the target budget once `N` is large. This is one step of the target:
it is the part of the signed difference carried by the intermediate shifts. -/
theorem split_intermediate_shift_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 3) := by
  sorry

/-- LEAF, OPEN. Third range only. Tuple differences larger than `N` in absolute value. The
averaged correlation error with both sums restricted to those tuples is at most a third of the
target budget once `N` is large. This is one step of the target: it is the part of the signed
difference carried by the long shifts, where the shift exceeds the summation range itself. -/
theorem split_large_shift_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 3) := by
  sorry

/-- ASSEMBLY. The sealed statement `Display5PlainExpansion`, from the three range leaves: split the
tuple sum by the size of `dif x`, apply each leaf to its range and add the three bounds. The
constant `θ₀ = 1/4` is the witness, and no `sorry` is used. -/
theorem display5_plain_expansion_split : Display5PlainExpansion := by
  classical
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₁, h₁⟩ := split_small_shift_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₂, h₂⟩ := split_intermediate_shift_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₃, h₃⟩ := split_large_shift_bound θ hθ hθ4 k hk δ hδ
  refine ⟨max (max N₁ N₂) N₃, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N :=
    le_trans (le_trans (le_max_left N₁ N₂) (le_max_left (max N₁ N₂) N₃)) hN
  have hN₂ : N₂ ≤ N :=
    le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) N₃)) hN
  have hN₃ : N₃ ≤ N := le_trans (le_max_right (max N₁ N₂) N₃) hN
  let T : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :=
    Finset.univ.filter (fun x => LeanLab.Linnik.Decomp1532a.dif x ≠ 0)
  let g : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re
  let w : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
      (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  let p1 : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ
  let p2 : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)
  have H₁ : |(T.filter p1).sum g - (T.filter p1).sum w| ≤ M * (δ / 3) := by
    simpa only [T, g, w, M, p1, Finset.filter_filter] using h₁ N hN₁
  have H₂ : |((T.filter (fun x => ¬ p1 x)).filter p2).sum g -
      ((T.filter (fun x => ¬ p1 x)).filter p2).sum w| ≤ M * (δ / 3) := by
    simpa only [T, g, w, M, p1, p2, Finset.filter_filter] using h₂ N hN₂
  have H₃ : |((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum g -
      ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum w| ≤ M * (δ / 3) := by
    simpa only [T, g, w, M, p1, p2, Finset.filter_filter] using h₃ N hN₃
  have hsplit : ∀ F : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ,
      T.sum F = (T.filter p1).sum F
        + ((T.filter (fun x => ¬ p1 x)).filter p2).sum F
        + ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum F := by
    intro F
    have e1 : (T.filter p1).sum F + (T.filter (fun x => ¬ p1 x)).sum F = T.sum F :=
      Finset.sum_filter_add_sum_filter_not T p1 F
    have e2 : ((T.filter (fun x => ¬ p1 x)).filter p2).sum F +
        ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum F =
        (T.filter (fun x => ¬ p1 x)).sum F :=
      Finset.sum_filter_add_sum_filter_not (T.filter (fun x => ¬ p1 x)) p2 F
    linarith
  have hA := hsplit g
  have hB := hsplit w
  have key : |T.sum g - T.sum w| ≤ M * δ := by
    have step : T.sum g - T.sum w =
        ((T.filter p1).sum g - (T.filter p1).sum w)
          + ((((T.filter (fun x => ¬ p1 x)).filter p2).sum g -
              ((T.filter (fun x => ¬ p1 x)).filter p2).sum w)
            + (((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum g -
              ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum w)) := by
      rw [hA, hB]; ring
    rw [step]
    have t1 := abs_add_le ((T.filter p1).sum g - (T.filter p1).sum w)
      ((((T.filter (fun x => ¬ p1 x)).filter p2).sum g -
          ((T.filter (fun x => ¬ p1 x)).filter p2).sum w)
        + (((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum g -
          ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum w))
    have t2 := abs_add_le
      (((T.filter (fun x => ¬ p1 x)).filter p2).sum g -
        ((T.filter (fun x => ¬ p1 x)).filter p2).sum w)
      (((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum g -
        ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum w)
    have hb₁ := H₁
    have hb₂ := H₂
    have hb₃ := H₃
    linarith
  simpa only [T, g, w, M] using key
