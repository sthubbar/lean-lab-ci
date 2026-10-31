import Mathlib
import LeanLab.Ternary78.Bennett.NTChi
import LeanLab.Ternary78.Threshold

namespace LeanLab.Ternary78.Threshold
open Real

theorem partial_summation_lemma {k : ℕ} (A B : ℕ → ℝ) :
    ∑ i ∈ Finset.range k, (A (i + 1) - A i) * B (i + 1) =
    (if k = 0 then 0 else A k * B k - A 0 * B 1 + ∑ i ∈ Finset.range (k - 1), A (i + 1) * (B (i + 1) - B (i + 2))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rcases k with _ | k'
    · simp; ring
    · have hk : k' + 1 - 1 = k' := rfl
      rw [hk] at ih
      have ih2 : ∑ i ∈ Finset.range (k' + 1), (A (i + 1) - A i) * B (i + 1) =
          A (k' + 1) * B (k' + 1) - A 0 * B 1 + ∑ i ∈ Finset.range k', A (i + 1) * (B (i + 1) - B (i + 2)) := by
        have : (if k' + 1 = 0 then (0:ℝ) else A (k' + 1) * B (k' + 1) - A 0 * B 1 + ∑ i ∈ Finset.range k', A (i + 1) * (B (i + 1) - B (i + 2))) = A (k' + 1) * B (k' + 1) - A 0 * B 1 + ∑ i ∈ Finset.range k', A (i + 1) * (B (i + 1) - B (i + 2)) := by
          apply ite_eq_right_iff.mpr; omega
        rw [this] at ih
        exact ih
      have e2 : (if k' + 1 + 1 = 0 then (0:ℝ) else A (k' + 1 + 1) * B (k' + 1 + 1) - A 0 * B 1 + ∑ i ∈ Finset.range (k' + 1 + 1 - 1), A (i + 1) * (B (i + 1) - B (i + 2))) = A (k' + 1 + 1) * B (k' + 1 + 1) - A 0 * B 1 + ∑ i ∈ Finset.range (k' + 1 + 1 - 1), A (i + 1) * (B (i + 1) - B (i + 2)) := by
        apply ite_eq_right_iff.mpr; omega
      rw [ih2, e2]
      have hk2 : k' + 1 + 1 - 1 = k' + 1 := rfl
      rw [hk2]
      have hs : ∑ i ∈ Finset.range (k' + 1), A (i + 1) * (B (i + 1) - B (i + 2)) =
          ∑ i ∈ Finset.range k', A (i + 1) * (B (i + 1) - B (i + 2)) + A (k' + 1) * (B (k' + 1) - B (k' + 2)) :=
        Finset.sum_range_succ _ _
      rw [hs]
      ring

theorem sum_lower_bound_of_counts {k : ℕ} (N_low : ℕ → ℝ) (N_actual : ℕ → ℝ)
    (f : ℕ → ℝ)
    (h_low : ∀ i, N_low i ≤ N_actual i)
    (h_f_mono : ∀ i, f (i + 1) ≤ f i)
    (h_f_nonneg : ∀ i, 0 ≤ f i)
    (h_N_low_zero : N_low 0 = 0)
    (h_N_actual_zero : N_actual 0 = 0) :
    ∑ i ∈ Finset.range k, (N_low (i + 1) - N_low i) * f (i + 1) ≤
    ∑ i ∈ Finset.range k, (N_actual (i + 1) - N_actual i) * f (i + 1) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk]; simp
  have e1 : ∑ i ∈ Finset.range k, (N_low (i + 1) - N_low i) * f (i + 1) =
      N_low k * f k - N_low 0 * f 1 + ∑ i ∈ Finset.range (k - 1), N_low (i + 1) * (f (i + 1) - f (i + 2)) := by
    have := partial_summation_lemma N_low f (k := k)
    have hz : (if k = 0 then (0:ℝ) else N_low k * f k - N_low 0 * f 1 + ∑ i ∈ Finset.range (k - 1), N_low (i + 1) * (f (i + 1) - f (i + 2))) = N_low k * f k - N_low 0 * f 1 + ∑ i ∈ Finset.range (k - 1), N_low (i + 1) * (f (i + 1) - f (i + 2)) := by
      apply ite_eq_right_iff.mpr; intro hc; exact False.elim (hk.ne' hc)
    rw [hz] at this
    exact this
  have e2 : ∑ i ∈ Finset.range k, (N_actual (i + 1) - N_actual i) * f (i + 1) =
      N_actual k * f k - N_actual 0 * f 1 + ∑ i ∈ Finset.range (k - 1), N_actual (i + 1) * (f (i + 1) - f (i + 2)) := by
    have := partial_summation_lemma N_actual f (k := k)
    have hz : (if k = 0 then (0:ℝ) else N_actual k * f k - N_actual 0 * f 1 + ∑ i ∈ Finset.range (k - 1), N_actual (i + 1) * (f (i + 1) - f (i + 2))) = N_actual k * f k - N_actual 0 * f 1 + ∑ i ∈ Finset.range (k - 1), N_actual (i + 1) * (f (i + 1) - f (i + 2)) := by
      apply ite_eq_right_iff.mpr; intro hc; exact False.elim (hk.ne' hc)
    rw [hz] at this
    exact this
  rw [e1, e2, h_N_low_zero, h_N_actual_zero]
  simp only [zero_mul, sub_zero]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right (h_low k) (h_f_nonneg k)
  · apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right (h_low (i + 1))
    linarith [h_f_mono (i + 1)]

end LeanLab.Ternary78.Threshold
