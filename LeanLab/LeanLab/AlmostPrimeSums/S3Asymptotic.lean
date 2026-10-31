/-
AI-written Lean code, OpenAI Codex, task33, 2026-10-23, T1.
P0072 Togashi and Uchiyama 1964, Section 5 p. 67.
The finite sum of S3Bound.S3_card_le has order at most N to the power 5/6.
The inverse square tail is enlarged from primes to all positive integers.
Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.S3Bound

open Finset
open LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5

namespace LeanLab.AlmostPrimeSums.S3Asymptotic

/-- The inverse square tail used in Section 5 p. 67. -/
lemma sum_inv_sq_le (N k : ℕ) (hk : ∀ q ∈ Qset N, k < q) :
    (∑ q ∈ Qset N, ((q : ℝ) ^ 2)⁻¹) ≤ 2 / ((k : ℝ) + 1) := by
  calc
    _ ≤ ∑ q ∈ Ioo k (N + 1), ((q : ℝ) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact mem_Ioo.mpr ⟨hk q hq, mem_range.mp (mem_filter.mp hq).1⟩
      · intro q _ _
        positivity
    _ ≤ _ := sum_Ioo_inv_sq_le k (N + 1)

/-- A tail bound for the exact finite sum in S3_card_le. -/
lemma finite_sum_le (N k : ℕ) (hk : ∀ q ∈ Qset N, k < q) :
    ((∑ q ∈ Qset N, 2 * (N / q ^ 2 + 1) : ℕ) : ℝ) ≤
      4 * N / ((k : ℝ) + 1) + 2 * (Qset N).card := by
  calc
    _ ≤ ∑ q ∈ Qset N, 2 * ((N : ℝ) / (q : ℝ) ^ 2 + 1) := by
      push_cast
      apply sum_le_sum
      intro q hq
      gcongr
      exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := N) (n := q ^ 2))
    _ = 2 * N * (∑ q ∈ Qset N, ((q : ℝ) ^ 2)⁻¹) + 2 * (Qset N).card := by
      simp_rw [div_eq_mul_inv, mul_add, sum_add_distrib, ← mul_assoc, ← mul_sum]
      simp
    _ ≤ 2 * N * (2 / ((k : ℝ) + 1)) + 2 * (Qset N).card := by
      gcongr
      exact sum_inv_sq_le N k hk
    _ = _ := by ring

/-- The lower cutoff in Qset is the real sixth root of N. -/
lemma sixth_root_lt {N q : ℕ} (hq : q ∈ Qset N) :
    (N : ℝ) ^ (1 / 6 : ℝ) < q := by
  have h6 : (N : ℝ) < (q : ℝ) ^ 6 := by
    exact_mod_cast (mem_filter.mp hq).2.2.1
  have h := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ N) h6 (by norm_num : (0 : ℝ) < 1 / 6)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ q)] at h
  norm_num at h
  exact h

/-- The upper cutoff in Qset is the real cube root of N. -/
lemma le_third_root {N q : ℕ} (hq : q ∈ Qset N) :
    (q : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
  have h3 : (q : ℝ) ^ 3 ≤ N := by
    exact_mod_cast (mem_filter.mp hq).2.2.2.1
  have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 3) h3
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ q)] at h
  norm_num at h
  exact h

/-- There are at most N to the power one third possible q. -/
lemma card_Qset_le (N : ℕ) : (Qset N).card ≤ ⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊ := by
  calc
    _ ≤ (Icc 1 ⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊).card := by
      apply card_le_card
      intro q hq
      exact mem_Icc.mpr ⟨(mem_filter.mp hq).2.1.one_lt.le,
        (Nat.le_floor_iff (by positivity)).mpr (le_third_root hq)⟩
    _ = _ := by simp

/-- An explicit version of the p. 67 asymptotic for the finite sum. -/
theorem finite_sum_le_six_rpow {N : ℕ} (hN : 1 ≤ N) :
    ((∑ q ∈ Qset N, 2 * (N / q ^ 2 + 1) : ℕ) : ℝ) ≤
      6 * (N : ℝ) ^ (5 / 6 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let k := ⌊(N : ℝ) ^ (1 / 6 : ℝ)⌋₊
  have hk : ∀ q ∈ Qset N, k < q := by
    intro q hq
    exact (Nat.floor_lt (by positivity)).mpr (sixth_root_lt hq)
  have htail := finite_sum_le N k hk
  have hcard : ((Qset N).card : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    exact (Nat.cast_le.mpr (card_Qset_le N)).trans (Nat.floor_le (by positivity))
  have hden : (N : ℝ) ^ (1 / 6 : ℝ) ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hdiv : 4 * (N : ℝ) / ((k : ℝ) + 1) ≤ 4 * (N : ℝ) / (N : ℝ) ^ (1 / 6 : ℝ) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have heq : (N : ℝ) / (N : ℝ) ^ (1 / 6 : ℝ) = (N : ℝ) ^ (5 / 6 : ℝ) := by
    rw [show (5 / 6 : ℝ) = 1 - 1 / 6 by norm_num, Real.rpow_sub hN0, Real.rpow_one]
  have hthird : (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  simp only [mul_div_assoc] at hdiv
  rw [heq] at hdiv
  rw [← mul_div_assoc] at hdiv
  linarith

example : 3 ∈ Qset 28 ∧ (∀ q ∈ Qset 28, 1 < q) := by decide

example : ((∑ q ∈ Qset 28, 2 * (28 / q ^ 2 + 1) : ℕ) : ℝ) = 8 := by
  exact_mod_cast (by decide : (∑ q ∈ Qset 28, 2 * (28 / q ^ 2 + 1) : ℕ) = 8)

example : (8 : ℝ) ≤ 6 * (28 : ℝ) ^ (5 / 6 : ℝ) := by
  have hsum : (∑ q ∈ Qset 28, 2 * (28 / q ^ 2 + 1) : ℕ) = 8 := by decide
  have h := finite_sum_le_six_rpow (N := 28) (by norm_num)
  rw [hsum] at h
  exact h

/-- S3 has the same explicit bound. -/
theorem S3_card_le_six_rpow {N : ℕ} (hN : 1 ≤ N) :
    ((S3set N).card : ℝ) ≤ 6 * (N : ℝ) ^ (5 / 6 : ℝ) := by
  exact (Nat.cast_le.mpr (S3Bound.S3_card_le N)).trans (finite_sum_le_six_rpow hN)

/-- The finite sum in S3_card_le has order N to the power 5/6. -/
theorem finite_sum_isBigO :
    (fun N : ℕ => ((∑ q ∈ Qset N, 2 * (N / q ^ 2 + 1) : ℕ) : ℝ))
      =O[Filter.atTop] (fun N : ℕ => (N : ℝ) ^ (5 / 6 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨6, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact finite_sum_le_six_rpow hN

/-- Section 5 p. 67: S3 has order N to the power 5/6. -/
theorem S3_card_isBigO :
    (fun N : ℕ => ((S3set N).card : ℝ))
      =O[Filter.atTop] (fun N : ℕ => (N : ℝ) ^ (5 / 6 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨6, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact S3_card_le_six_rpow hN

end LeanLab.AlmostPrimeSums.S3Asymptotic

#print axioms LeanLab.AlmostPrimeSums.S3Asymptotic.sum_inv_sq_le

#print axioms LeanLab.AlmostPrimeSums.S3Asymptotic.finite_sum_le

#print axioms LeanLab.AlmostPrimeSums.S3Asymptotic.sixth_root_lt

#print axioms LeanLab.AlmostPrimeSums.S3Asymptotic.le_third_root

#print axioms LeanLab.AlmostPrimeSums.S3Asymptotic.card_Qset_le

#print axioms LeanLab.AlmostPrimeSums.S3Asymptotic.finite_sum_le_six_rpow

#print axioms LeanLab.AlmostPrimeSums.S3Asymptotic.S3_card_le_six_rpow

#print axioms LeanLab.AlmostPrimeSums.S3Asymptotic.finite_sum_isBigO

#print axioms LeanLab.AlmostPrimeSums.S3Asymptotic.S3_card_isBigO
