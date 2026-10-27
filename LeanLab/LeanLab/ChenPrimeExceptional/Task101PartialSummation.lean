/-
AI wrote this Lean code for CODEX task101.
P0039 Lemma 5.2, page 29. Explicit finite partial-summation bounds.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101FourierSieve
import Mathlib.Algebra.BigOperators.Module

open Finset

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- The total variation of the first n values of a weight. -/
def variation (w : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n - 1), ‖w (i + 1) - w i‖

/-- Partial summation turns a prefix-sum bound into a weighted-sum bound. -/
theorem weighted_sum_bound (a w : ℕ → ℂ) (n : ℕ) {M : ℝ}
    (hM : ∀ k ≤ n, ‖∑ i ∈ range k, a i‖ ≤ M) :
    ‖∑ i ∈ range n, w i * a i‖ ≤ (‖w (n - 1)‖ + variation w n) * M := by
  have hp := sum_range_by_parts w a n
  simp only [smul_eq_mul] at hp
  rw [hp]
  calc
    _ ≤ ‖w (n - 1) * ∑ i ∈ range n, a i‖ +
        ‖∑ i ∈ range (n - 1), (w (i + 1) - w i) * ∑ j ∈ range (i + 1), a j‖ :=
      norm_sub_le _ _
    _ ≤ ‖w (n - 1)‖ * M + ∑ i ∈ range (n - 1), ‖w (i + 1) - w i‖ * M := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM n le_rfl) (norm_nonneg _)
      · refine (norm_sum_le _ _).trans (sum_le_sum ?_)
        intro i hi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM (i + 1) (by simp only [mem_range] at hi; omega))
          (norm_nonneg _)
    _ = _ := by rw [variation, ← sum_mul]; ring

/-- Inversion increases total variation by at most the inverse square of a lower norm bound. -/
theorem inverse_variation_bound (w : ℕ → ℂ) (n : ℕ) {L : ℝ}
    (hL : 0 < L) (hw : ∀ i < n, L ≤ ‖w i‖) :
    variation (fun i => (w i)⁻¹) n ≤ variation w n / L ^ 2 := by
  unfold variation
  rw [sum_div]
  apply sum_le_sum
  intro i hi
  have hi0 : i < n := by simp only [mem_range] at hi; omega
  have hi1 : i + 1 < n := by simp only [mem_range] at hi; omega
  have hw0 : w i ≠ 0 := norm_pos_iff.mp (hL.trans_le (hw i hi0))
  have hw1 : w (i + 1) ≠ 0 := norm_pos_iff.mp (hL.trans_le (hw (i + 1) hi1))
  have he := dist_inv_inv₀ hw1 hw0
  simp only [dist_eq_norm] at he
  rw [he]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hL)
  nlinarith [hw i hi0, hw (i + 1) hi1]

/-- Reverse partial summation recovers an unweighted sum from the weighted prefixes. -/
theorem unweighted_sum_bound (a w : ℕ → ℂ) (n : ℕ) {L M : ℝ}
    (hL : 0 < L) (hw : ∀ i < n, L ≤ ‖w i‖)
    (hM : ∀ k ≤ n, ‖∑ i ∈ range k, w i * a i‖ ≤ M) :
    ‖∑ i ∈ range n, a i‖ ≤ (1 / L + variation w n / L ^ 2) * M := by
  have hM0 : 0 ≤ M := by simpa using hM 0 (Nat.zero_le n)
  by_cases hn : n = 0
  · subst n
    simp only [range_zero, sum_empty, norm_zero, variation]
    positivity
  have hn0 : n - 1 < n := by omega
  have h := weighted_sum_bound (fun i => w i * a i) (fun i => (w i)⁻¹) n hM
  have heq : (∑ i ∈ range n, (w i)⁻¹ * (w i * a i)) = ∑ i ∈ range n, a i := by
    apply sum_congr rfl
    intro i hi
    have hwi : w i ≠ 0 := norm_pos_iff.mp (hL.trans_le (hw i (mem_range.mp hi)))
    rw [← mul_assoc, inv_mul_cancel₀ hwi, one_mul]
  rw [heq] at h
  refine h.trans (mul_le_mul_of_nonneg_right (add_le_add ?_ (inverse_variation_bound w n hL hw)) hM0)
  rw [norm_inv, one_div]
  simpa only [one_div] using one_div_le_one_div_of_le hL (hw _ hn0)

/-- Explicit scaled version of the two partial-summation inequalities in Lemma 5.2. -/
theorem lemma52_discrete (a w : ℕ → ℂ) (n : ℕ) {H c W V M U : ℝ}
    (hH : 0 < H) (hc : 0 < c)
    (hlo : ∀ i < n, c * H ≤ ‖w i‖)
    (hhi : ‖w (n - 1)‖ ≤ W * H) (hvar : variation w n ≤ V * H)
    (hM : ∀ k ≤ n, ‖∑ i ∈ range k, a i‖ ≤ M)
    (hU : ∀ k ≤ n, ‖∑ i ∈ range k, w i * a i‖ ≤ U) :
    ‖∑ i ∈ range n, w i * a i‖ ≤ (W + V) * H * M ∧
      ‖∑ i ∈ range n, a i‖ ≤ ((1 / c + V / c ^ 2) / H) * U := by
  have hM0 : 0 ≤ M := by simpa using hM 0 (Nat.zero_le n)
  have hU0 : 0 ≤ U := by simpa using hU 0 (Nat.zero_le n)
  constructor
  · refine (weighted_sum_bound a w n hM).trans ?_
    apply mul_le_mul_of_nonneg_right _ hM0
    nlinarith
  · refine (unweighted_sum_bound a w n (mul_pos hc hH) hlo hU).trans ?_
    apply mul_le_mul_of_nonneg_right _ hU0
    calc
      _ ≤ 1 / (c * H) + (V * H) / (c * H) ^ 2 :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hvar (sq_nonneg _))
      _ = _ := by field_simp [hc.ne', hH.ne']

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.weighted_sum_bound
#print axioms LeanLab.ChenPrimeExceptional.Task101.inverse_variation_bound
#print axioms LeanLab.ChenPrimeExceptional.Task101.unweighted_sum_bound
#print axioms LeanLab.ChenPrimeExceptional.Task101.lemma52_discrete
