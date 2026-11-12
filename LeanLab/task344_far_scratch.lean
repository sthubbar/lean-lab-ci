import LeanLab.Linnik.Decomp1532b

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)

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

/-- LEAF, OPEN. First piece of the long shift range, the near one: shifts above the summation range
`N` but no larger than twice it. This is the step of the target where the difference of the two
exponent sums on the two sides of a pair is still of the order of `N`, so every coefficient of the
squared exponential sum contributes, and only the oscillation of the phase over the complement of
the major arcs can save anything. The total of the correlations over the complement of the major
arcs restricted to these tuples is at most a ninth of the budget factor once `N` is large. -/
theorem large_shift_near_sum_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ),
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  sorry

/-- LEAF, OPEN. Second piece of the long shift range, the middle one: shifts above `2 N` but no
larger than `N ^ (3/2)`. This is the step of the target where the difference of the two exponent
sums is larger than the summation range, so the coefficient of the squared exponential sum at that
shift has already dropped out of the diagonal and the correlation has to come from the oscillation
of the phase alone, while the shift is still small enough that the phase moves by a whole winding
across a major arc. The total of the correlations over the complement of the major arcs restricted
to these tuples is at most a ninth of the budget factor once `N` is large. -/
theorem large_shift_middle_sum_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2),
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  sorry

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
    exact mul_lt_mul_of_pos_right hhalf hNpos
  have hempty :
      (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2))) :
        Finset.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2))) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx
    have hp := (Finset.mem_filter.mp hx).2
    have habs := dif_abs_le_kN (by omega) x
    have hfar := not_le.mp hp.2.2.2
    exact (not_lt_of_ge habs) (hfar.trans_le habs)
  rw [hempty, Finset.sum_empty, abs_zero]
  have hM : 0 ≤ 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 := by
    positivity
  have hδ9 : 0 ≤ δ / 9 := div_nonneg hδ.le (by norm_num)
  exact mul_nonneg hM hδ9


#print axioms large_shift_far_sum_bound
