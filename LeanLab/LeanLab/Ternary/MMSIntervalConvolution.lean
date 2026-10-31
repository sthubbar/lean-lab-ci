/-
P0028, https://arxiv.org/abs/1610.02017, section 4.3, page 9.
The interval convolution agrees with the full integer convolution of zero extensions.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSIntervalLift
import LeanLab.Ternary.MMSFourierError
namespace LeanLab.Ternary.MMS
open Finset

/-- Pairing the zero extension with any function gives the original interval sum. -/
theorem intervalLift_sum_mul (N : ℕ) (f : ℕ → ℝ) (F : ℤ → ℝ) :
    (∑ a ∈ (intervalLift N f).support, intervalLift N f a * F a) =
      ∑ a ∈ Icc 1 N, f a * F a := by
  change (Finsupp.linearCombination ℝ F) (intervalLift N f) = _
  simp [intervalLift, smul_eq_mul]

/-- The third summand in the interval convolution is the integer zero extension. -/
theorem intervalLift_sub_pair (N n a b : ℕ) (f : ℕ → ℝ) :
    intervalLift N f ((n : ℤ) - a - b) =
      if a + b < n ∧ n - (a + b) ≤ N then f (n - (a + b)) else 0 := by
  by_cases hab : a + b ≤ n
  · have he : (n : ℤ) - a - b = ((n - (a + b) : ℕ) : ℤ) := by omega
    rw [he, intervalLift_apply_nat]
    have hh : n - (a + b) ∈ Icc 1 N ↔ a + b < n ∧ n - (a + b) ≤ N := by
      simp only [mem_Icc]
      omega
    simp only [hh]
  · rw [intervalLift_apply_neg N f _ (by omega)]
    rw [ite_eq_right (by omega)]

/-- Full integer convolution of zero extensions equals the sealed interval convolution. -/
theorem int_triple_intervalLift (N n : ℕ) (f g h : ℕ → ℝ) :
    (∑ a ∈ (intervalLift N f).support, ∑ b ∈ (intervalLift N g).support,
      intervalLift N f a * intervalLift N g b * intervalLift N h ((n : ℤ) - a - b)) =
      conv3 N f g h n := by
  simp_rw [mul_assoc, ← mul_sum]
  rw [intervalLift_sum_mul]
  unfold conv3
  apply sum_congr rfl
  intro a ha
  rw [intervalLift_sum_mul, mul_sum]
  apply sum_congr rfl
  intro b hb
  rw [intervalLift_sub_pair]
  split_ifs <;> ring

end LeanLab.Ternary.MMS
