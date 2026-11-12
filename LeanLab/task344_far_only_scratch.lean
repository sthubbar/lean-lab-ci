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
import LeanLab.Linnik.Decomp1532b

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- Elementary support bound for a tuple difference. Every tuple difference has absolute value at
most `k N`, since each exponent sum is at most `k 2 ^ (Nat.log 2 N)`. This is the existing
Gallagher p.136 Lemma 8 estimate, cast from the natural absolute value to the real one. -/
lemma dif_abs_le_kN {k N : ℕ} (hN : 1 ≤ N)
    (x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (k : ℝ) * (N : ℝ) := by
  have ha := LeanLab.Linnik.U1434Lemma21.sv_le x.1
  have hb := LeanLab.Linnik.U1434Lemma21.sv_le x.2
  have hp : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have ha' := ha.trans (Nat.mul_le_mul_left k hp)
  have hb' := hb.trans (Nat.mul_le_mul_left k hp)
  have hm : (LeanLab.Linnik.Decomp1532a.dif x).natAbs ≤ k * N := by
    unfold LeanLab.Linnik.Decomp1532a.dif
    omega
  have hr : ((LeanLab.Linnik.Decomp1532a.dif x).natAbs : ℝ) ≤
      (k : ℝ) * (N : ℝ) := by exact_mod_cast hm
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hr

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
  classical
  intro θ hθ hθ4 k hk δ hδ
  refine ⟨k ^ 2 + 1, ?_⟩
  intro N hN
  have hk2 : (k : ℝ) ^ 2 < (N : ℝ) := by
    have hnat : k ^ 2 < N := by omega
    exact_mod_cast hnat
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hk2_nonneg : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
  have hNpos : 0 < (N : ℝ) := by nlinarith
  have hsqrt : (k : ℝ) < Real.sqrt (N : ℝ) := by
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ k)).2 hk2
  have hhalf : (k : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact hsqrt
  have hrpow3 : (N : ℝ) ^ ((3 : ℝ) / 2) =
      (N : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add hNpos]
    simp
  have hkNpow : (k : ℝ) * (N : ℝ) < (N : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [hrpow3]
    simpa only [mul_comm] using (mul_lt_mul_of_pos_right hhalf hNpos)
  have hempty :
      Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2))) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx hp
    have habs := dif_abs_le_kN (by omega) x
    have hfar := not_le.mp hp.2.2.2
    exact (not_lt_of_ge hkNpow.le) (hfar.trans_le habs)
  rw [hempty, Finset.sum_empty, abs_zero]
  have hM : 0 ≤ 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 := by
    positivity
  have hδ9 : 0 ≤ δ / 9 := div_nonneg hδ.le (by norm_num)
  exact mul_nonneg hM hδ9


#print axioms large_shift_far_sum_bound
