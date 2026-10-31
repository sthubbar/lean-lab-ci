import LeanLab.Romanov.Theorem

/-!
# The elementary mean singular product for differences of powers of two

AI wrote the Lean code. Known Romanov method. Gallagher 1975, page 138, display 2.
This makes the elementary input to the second moment explicit.
Binary Goldbach is OPEN.
-/

namespace LeanLab.Romanov

open Finset Real
open LeanLab.SchnirelmannGoldbach (singProd)

/-- Remove the power of two from a nonzero difference. -/
theorem singProd_pow_gap_le {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) :
    singProd (2 ^ l - 2 ^ k) ≤ 3 / 2 * singProd (2 ^ (l - k) - 1) := by
  have hsplit : 2 ^ l - 2 ^ k = 2 ^ k * (2 ^ (l - k) - 1) := by
    have hp : 2 ^ l = 2 ^ k * 2 ^ (l - k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp, Nat.mul_sub_one]
  rw [hsplit]
  calc singProd (2 ^ k * (2 ^ (l - k) - 1))
      ≤ singProd (2 ^ k) * singProd (2 ^ (l - k) - 1) :=
        singProd_mul_le (by positivity) (two_pow_sub_one_ne_zero (by omega))
    _ = 3 / 2 * singProd (2 ^ (l - k) - 1) := by
      rw [singProd_two_pow (by omega)]

/-- For a fixed first exponent, the mean weight of the remaining exponent differences. -/
theorem inner_Icc_le (K k : ℕ) :
    ∑ l ∈ Icc 1 K, (if k < l then singProd (2 ^ (l - k) - 1) else 0) ≤
      8 * log 2 * exp 13 * K := by
  calc ∑ l ∈ Icc 1 K, (if k < l then singProd (2 ^ (l - k) - 1) else 0)
      ≤ ∑ m ∈ Icc 1 K, singProd (2 ^ m - 1) := by
        rw [← sum_filter]
        rw [← sum_image (g := fun l => l - k) (f := fun m => singProd (2 ^ m - 1))]
        · apply sum_le_sum_of_subset_of_nonneg
          · intro m hm
            obtain ⟨l, hl, rfl⟩ := mem_image.mp hm
            simp only [mem_filter, mem_Icc] at hl
            simp only [mem_Icc]
            omega
          · intro m _ _
            exact singProd_nonneg _
        · intro a ha b hb hab
          simp only [mem_coe, mem_filter, mem_Icc] at ha hb
          simp only at hab
          omega
    _ ≤ 8 * log 2 * exp 13 * K := romanov_lemma K

/-- The mean singular product over strictly increasing positive exponents is quadratic. -/
theorem gap_singProd_mean (K : ℕ) :
    ∑ k ∈ Icc 1 K, ∑ l ∈ Icc 1 K,
      (if k < l then singProd (2 ^ l - 2 ^ k) else 0) ≤
      12 * log 2 * exp 13 * (K : ℝ) ^ 2 := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  calc ∑ k ∈ Icc 1 K, ∑ l ∈ Icc 1 K,
        (if k < l then singProd (2 ^ l - 2 ^ k) else 0)
      ≤ ∑ k ∈ Icc 1 K, (3 / 2 : ℝ) *
          ∑ l ∈ Icc 1 K, (if k < l then singProd (2 ^ (l - k) - 1) else 0) := by
        apply sum_le_sum
        intro k hk
        rw [mul_sum]
        apply sum_le_sum
        intro l hl
        by_cases hkl : k < l
        · simp only [ite_eq_left hkl]
          exact singProd_pow_gap_le (mem_Icc.mp hk).1 hkl
        · simp only [ite_eq_right hkl, mul_zero]
          exact le_rfl
    _ ≤ ∑ _k ∈ Icc 1 K, (3 / 2 : ℝ) * (8 * log 2 * exp 13 * K) := by
        apply sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (inner_Icc_le K k) (by norm_num)
    _ = 12 * log 2 * exp 13 * (K : ℝ) ^ 2 := by
        simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

/-- The full off-diagonal double mean is quadratic in the exponent cutoff. -/
theorem ordered_gap_singProd_mean (K : ℕ) :
    ∑ k ∈ Icc 1 K, ∑ l ∈ Icc 1 K,
      (if k ≠ l then singProd (2 ^ max k l - 2 ^ min k l) else 0) ≤
      24 * log 2 * exp 13 * (K : ℝ) ^ 2 := by
  have hpt (k l : ℕ) :
      (if k ≠ l then singProd (2 ^ max k l - 2 ^ min k l) else 0) =
      (if k < l then singProd (2 ^ l - 2 ^ k) else 0) +
      (if l < k then singProd (2 ^ k - 2 ^ l) else 0) := by
    rcases lt_trichotomy k l with h | h | h
    · simp [h.ne, h, not_lt_of_ge h.le, max_eq_right h.le, min_eq_left h.le]
    · subst l
      simp
    · simp [h.ne', h, not_lt_of_ge h.le, max_eq_left h.le, min_eq_right h.le]
  simp_rw [hpt, sum_add_distrib]
  rw [sum_comm (f := fun k l => if l < k then singProd (2 ^ k - 2 ^ l) else 0)]
  have h := gap_singProd_mean K
  linarith

end LeanLab.Romanov
