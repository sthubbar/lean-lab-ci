/-
Split of `LeanLab.Linnik.Decomp1532c.split_large_shift_bound`.

The sealed leaf `split_large_shift_bound` is the long shift range of the averaged major arc
correlation error: the tuples with difference larger than `N` in absolute value. Two reductions
remove everything in it that is not analysis, and one open estimate is left.

Reduction one, `large_shift_filter_iff`: for `N` at least one and `theta` in `(0, 1]` the scale
`N ^ theta` is at most `N`, so the three conjunct predicate of the sealed statement is the same
as `dif x != 0` together with `N < |dif x|`.

Reduction two, `large_shift_major_eq_neg_minor`: the full unit interval correlation of a shift
larger than `N` vanishes, so its major arc correlation equals minus its correlation over the
complement of the major arcs.

The open estimate, `large_shift_minor_sum_bound`, is the cancellation statement on the complement:
the total of those correlations over the long shifts is at most a third of the sealed budget once
`N` is large. It is the one step of this range that is not bookkeeping.

The singular side of the sealed difference needs no leaf: `large_shift_main_sum_eq_zero`, already
in the file split here, kills it on this range. Assembly: `split_large_shift_bound_split`, the
sealed statement, with no sorry.

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

/-- LEAF, OPEN. Reduction of the range predicate: for `N` at least one and `theta` in `(0, 1]` the
major arc scale `N ^ theta` does not exceed `N`, so on the long shift range the three conjunct
predicate of the sealed statement says exactly that the difference is nonzero and exceeds `N` in
absolute value. This is the first step of the split, an equivalence of predicates with no
estimate in it. -/
theorem large_shift_filter_iff (k N : ℕ) (hN : 1 ≤ N) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :
    (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ))) ↔
      (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
        (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|) := by
  sorry

/-- LEAF, OPEN. Support reduction, one tuple at a time: for a shift larger than `N` in absolute
value the full unit interval correlation vanishes, hence the major arc correlation of that shift
is minus its correlation over the complement of the major arcs. This is the second step of the
split and it is what turns the major arc sum into a sum over the complement. -/
theorem large_shift_major_eq_neg_minor (k N : ℕ) (θ : ℝ)
    (x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N))
    (hx : (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|) :
    (∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) =
      -(∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
        ‖Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) := by
  sorry

/-- LEAF, OPEN. The open estimate of this range: once `N` is large, the total over the long shifts
of the correlation over the complement of the major arcs is at most a third of the sealed budget
`2 N L ^ (2k) / log N ^ 2`. Each shift here exceeds `N`, so the phase oscillates over the
complement and the sum of the correlations is small. This is the analytic step of the split; the
two reductions above are what reduce the sealed statement to it. -/
theorem large_shift_minor_sum_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|,
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 3) := by
  sorry

/-- ASSEMBLY. The sealed statement `split_large_shift_bound`, from the three leaves of this split:
rewrite the range predicate (`large_shift_filter_iff`), drop the singular side, which is zero on
this range by `large_shift_main_sum_eq_zero`, replace each major arc correlation by minus its
correlation over the complement (`large_shift_major_eq_neg_minor`), and apply the one open
estimate (`large_shift_minor_sum_bound`). No sorry. -/
theorem split_large_shift_bound_split :
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
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₃, h₃⟩ := large_shift_minor_sum_bound θ hθ hθ4 k hk δ hδ
  refine ⟨max N₃ 1, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := le_trans (le_max_right N₃ 1) hN
  have hN₃ : N₃ ≤ N := le_trans (le_max_left N₃ 1) hN
  have hθ1 : θ ≤ 1 := by linarith
  have hfil : (univ : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N))).filter
      (fun x => LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ))) =
      univ.filter (fun x => LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
        (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|) :=
    Finset.filter_congr fun x _ => large_shift_filter_iff k N hN1 θ hθ hθ1 x
  have hfirst : (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
      LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)),
        ∫ α in majorArcs N ((N : ℝ) ^ θ),
          ‖Sg N α‖ ^ 2 *
            (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) =
      (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|,
          ∫ α in majorArcs N ((N : ℝ) ^ θ),
            ‖Sg N α‖ ^ 2 *
              (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) := by
    rw [hfil]
  have hmaj : (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|,
        ∫ α in majorArcs N ((N : ℝ) ^ θ),
          ‖Sg N α‖ ^ 2 *
            (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) =
      -(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|,
          ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
            ‖Sg N α‖ ^ 2 *
              (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x hx =>
      large_shift_major_eq_neg_minor k N θ x (mem_filter.mp hx).2.2
  show |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
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
      (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 3)
  rw [hfirst, large_shift_main_sum_eq_zero k N θ, sub_zero, hmaj, abs_neg]
  exact h₃ N hN₃
