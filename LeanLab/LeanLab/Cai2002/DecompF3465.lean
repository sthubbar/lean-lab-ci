/-
P0044, Cai 2002, task3465 split for target leaf118_sieve_three (Decomp118.lean, page 604, display 4.15).
Created for FREE-nv-glm6 task3465 on branch free-nv-glm6/task3465.

This file only adds new declarations; it edits no existing .lean file.
It contributes three leaves and one assembly:

  leaf_C_pos          0 < C N for every N (proved; twin constant positivity)
  leaf_int_bound      the exact display-4.15 integral constant is ≤ 0.15639 (proved; Taylor bound)
  leaf_sieve_three_main S3(N, 0.95) ≤ [exact integral constant] · K for all large even N (LEAF sorry)
  leaf118_sieve_three_F3465 the full task statement, proved from the leaves with no sorry

The sorry leaf is the analytic sieve step (linear sieve, switching, Wu 1993 and Huxley
short interval inputs are not formalized in LeanLab); it is left open for the other workers.
Binary Goldbach is open; AI wrote the Lean code.
-/

import LeanLab.Cai2002.Decomp118

open Filter Asymptotics Finset Real intervalIntegral Set
open scoped Topology

namespace LeanLab.Cai2002

/-- LEAF. Positivity of C(N) for every N: the twin prime constant is positive and each local
factor (p-1)/(p-2) with p > 2 is positive, so the finite product over the odd primes dividing
N is positive. One analytic fact about the scale factor; no sieve count is involved. -/
theorem leaf_C_pos (N : ℕ) : 0 < C N := by
  have h₁ : 0 < LeanLab.ChenExplicit.twinC := twinC_pos
  have h₂ : 0 < ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2) : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have h₃ : 2 < p := (Finset.mem_filter.mp hp).1
    have h₄ : 0 < (p : ℝ) - 1 := by linarith
    have h₅ : 0 < (p : ℝ) - 2 := by linarith
    exact div_pos h₄ h₅
  exact mul_pos h₁ h₂

/-- LEAF. Page 604 display 4.15 constant: the exact integral bound
8/(2·0.95−1) ∫₂^2.29 log(t−1)/t dt is below 0.15639, leaving slack to the printed 0.1564.
A pure real estimate from Mathlib's Taylor bound for log and an exact polynomial integral;
no sieve input and no dependence on N. -/
theorem leaf_int_bound :
    8 / (2 * (0.95 : ℝ) - 1) * ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t ≤ 0.15639 := by
  have hcont : ContinuousOn (fun t : ℝ => Real.log (t - 1) / t) (Set.uIcc 2 2.29) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht; show t - 1 ≠ 0; have := ht.1; intro h'; linarith
    · exact continuousOn_id
    · intro t ht; have := ht.1; intro h'; linarith
  have hI : ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t ≤
      ∫ t in (2 : ℝ)..2.29, Lp (t - 2) * Qp (t - 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable)
    · apply Continuous.intervalIntegrable
      unfold Lp Qp; fun_prop
    · intro t ht; exact integrand_le ht
  have hJ : ∫ t in (2 : ℝ)..2.29, Lp (t - 2) * Qp (t - 2) =
      ∫ u in (0 : ℝ)..0.29, Lp u * Qp u := by
    rw [intervalIntegral.integral_comp_sub_right (fun u => Lp u * Qp u)]
    norm_num
  rw [hJ, integral_LpQp] at hI
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cP] at hI
  norm_num at hI ⊢
  have h8 : (0 : ℝ) < 8 / (2 * 0.95 - 1) := by norm_num
  calc
    (8 / (2 * (0.95 : ℝ) - 1) * ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t : ℝ)
      ≤ (8 / (2 * (0.95 : ℝ) - 1) * ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t : ℝ) := le_refl _
    _ ≤ 0.15639 := by
      have := mul_le_mul_of_nonneg_left hI h8.le
      norm_num at this ⊢
      linarith

/-- LEAF. Page 604 display 4.15 sieve step: for all sufficiently large even N, S₃(N, 0.95) is at most
the exact display-4.15 integral constant times K = C(N) N^0.95 / log² N.
The remaining weakening from this exact constant to the printed 0.1564 is a separate constant-arithmetic
step and is not part of this leaf. Requires the linear sieve, the switching identity, Wu's mean value
theorem and Huxley's short interval prime theorem, which are not formalized in LeanLab. -/
theorem leaf_sieve_three_main :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, Even N → N0 ≤ N →
      (S3 N 0.95 : ℝ) ≤
        (8 / (2 * (0.95 : ℝ) - 1) * ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t) *
          (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  sorry

theorem leaf118_sieve_three_F3465 :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S3 N 0.95 : ℝ) ≤
        0.1564 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  obtain ⟨N0, hN0ge2, hN0⟩ := leaf_sieve_three_main
  refine' ⟨N0, fun N he hN => _⟩
  have hN2 : 2 ≤ N := by linarith
  have hKpos : 0 < (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2 : ℝ) := by
    have h₁ : 0 < C N := leaf_C_pos N
    have h₂ : 0 < (N : ℝ) ^ (0.95 : ℝ) := by positivity
    have h₃ : 0 < Real.log N := Real.log_pos (by linarith)
    have h₄ : 0 < Real.log N ^ 2 := by positivity
    exact div_pos (mul_pos h₁ h₂) h₄
  calc
    (S3 N 0.95 : ℝ) ≤
        (8 / (2 * (0.95 : ℝ) - 1) * ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t) *
          (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
      exact hN0 N he hN
    _ ≤ 0.15639 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
      have hc : 8 / (2 * (0.95 : ℝ) - 1) * ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t ≤ 0.15639 := by
        exact leaf_int_bound
      have hK' : 0 ≤ (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2 : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_left hc hK'
    _ ≤ 0.1564 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
      have hc : (0.15639 : ℝ) ≤ 0.1564 := by norm_num
      have hK' : 0 ≤ (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2 : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_left hc hK'

end LeanLab.Cai2002
