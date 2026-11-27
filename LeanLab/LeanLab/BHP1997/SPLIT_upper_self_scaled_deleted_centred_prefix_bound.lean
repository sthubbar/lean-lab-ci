/-
Split of the OPEN leaf `upper_self_scaled_deleted_centred_prefix_bound` of
SPLIT_upper_self_scaled_principal_centred_prefix_bound into a MEDIUM leaf, a HARD leaf and a
proved conversion lemma, with an assembly that carries that same statement, proved from them and
using no sorry.

Source: P0069 Baker, Harman and Pintz 1997, Section 5, page 53. The deleted part of k_m at the
self scale Y = m counts m = p1 p2 p3 n4 with m^c1 ≤ p3 < p2 < p1 < m^c4, n4 free of primes below
p3, and the exponent triple in the deleted set E. The paper evaluates its mass by the prime number
theorem and partial summation, which sees m as a product of distinct primes times n4. Integers m
with a repeated prime factor p ≥ m^c1 are not counted correctly by that heuristic, and the paper
discards them silently as a lower order error.

Leaf 1, MEDIUM: the terms with m divisible by p^2 for some prime p ≥ m^c1 contribute O(Y^(1-c1)).
Leaf 2, HARD: the main part, m with no repeated prime factor above m^c1, has the centred prefix
bound at the density upperDeletedIntegral over log Y, by the PNT and partial summation.
Lemma, PROVED here: Y^(1-c1) is eventually below C Y (log x)^(-A) for every A.

This file adds no definition and edits no existing file. AI wrote the Lean code.
Binary Goldbach is OPEN.
-/
import LeanLab.BHP1997.SPLIT_upper_self_scaled_principal_centred_prefix_bound

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d

/-- Helper: upperC1 ε is positive and less than 1 -/
lemma upperC1_spec {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    0 < upperC1 ε ∧ upperC1 ε < 1 := by
  have h₁ : 0 < upperC1 ε := by
    rw [show upperC1 ε = (1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5)) : ℝ) / 15 - ε by
      rfl]
    norm_num at hε8 ⊢
    <;> linarith
  have h₂ : upperC1 ε < 1 := by
    rw [show upperC1 ε = (1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5)) : ℝ) / 15 - ε by rfl]
    norm_num at hε8 ⊢
    <;> linarith
  exact ⟨h₁, h₂⟩

/-- Helper: upperK - upperKept is bounded between 0 and a constant -/
lemma diff_bounded {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ,
      0 ≤ (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) ∧
      (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) ≤ K := by
  use 1 + 18 + 18 ^ 2 + 18 ^ 3
  constructor
  · norm_num
  intro m
  have h₁ : 0 ≤ (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) := by
    have h₂ : upperKept ε (m : ℝ) m ≤ upperK ε (m : ℝ) m := upper_kept_le ε (m : ℝ) m
    linarith
  have h₂ : (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) ≤ (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by
    have h₃ : upperRawWeight ε (m : ℝ) m = upperRough m ((m : ℝ) ^ upperC1 ε) + (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) := by
      rw [upper_raw_eq_rough_add_deleted ε (by
        by_cases hm : m = 0
        · simp_all [upperRawWeight, upperRough, upperK, upperKept, upperG, upperH, upperJ, Nat.cast_zero]
          <;> norm_num
        · positivity)] m
      <;> simp_all [upperDeletedSum]
      <;> ring
    have h₄ : |upperRawWeight ε (m : ℝ) m| ≤ (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by
      by_cases hm : m = 0
      · simp_all [upperRawWeight, upperRough, upperK, upperKept, upperG, upperH, upperJ, Nat.cast_zero]
        <;> norm_num
      · have h₅ : 2 ≤ (m : ℝ) := by
          norm_cast
          <;> omega
        have h₆ : (m : ℝ) ≤ 2 * (m : ℝ) := by linarith
        have h₇ : |upperRawWeight ε (m : ℝ) m| ≤ (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by
          have h₈ := upper_raw_abs_le hε8 (by linarith) hm (by linarith)
          simpa [abs_le] using h₈
        exact h₇
    have h₅ : 0 ≤ upperRough m ((m : ℝ) ^ upperC1 ε) := upperRough_nonneg _ _
    have h₆ : upperRough m ((m : ℝ) ^ upperC1 ε) ≤ 1 := upperRough_le_one _ _
    have h₇ : upperRawWeight ε (m : ℝ) m ≤ (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by
      linarith [abs_le.mp h₄]
    have h₈ : upperRawWeight ε (m : ℝ) m ≥ -(1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by
      linarith [abs_le.mp h₄]
    have h₉ : upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m = upperRawWeight ε (m : ℝ) m - upperRough m ((m : ℝ) ^ upperC1 ε) := by linarith
    rw [h₉]
    linarith
  exact ⟨h₁, h₂⟩

/-- Helper: log ratio bound -/
lemma log_ratio_le_two {Y : ℝ} (hY : 2 ≤ Y) : Real.log (2 * Y) / Real.log Y ≤ 2 := by
  have h₁ : Real.log (2 * Y) = Real.log 2 + Real.log Y := by
    rw [Real.log_mul (by linarith) (by linarith)]
  rw [h₁]
  have h₂ : 0 < Real.log Y := Real.log_pos (by linarith)
  have h₃ : Real.log 2 / Real.log Y + 1 ≤ 2 := by
    have h₄ : Real.log 2 ≤ Real.log Y := Real.log_le_log (by linarith) (by linarith)
    have h₅ : 0 < Real.log Y := Real.log_pos (by linarith)
    have h₆ : Real.log 2 / Real.log Y ≤ 1 := by
      rw [div_le_iff h₅]
      linarith
    linarith
  have h₄ : Real.log 2 / Real.log Y + 1 = Real.log 2 / Real.log Y + 1 := rfl
  have h₅ : (Real.log 2 + Real.log Y) / Real.log Y = Real.log 2 / Real.log Y + 1 := by
    field_simp [h₂.ne']
    <;> ring
  rw [h₅] at *
  linarith

/-- Helper: cardinality bound for numbers with repeated prime factors -/
lemma card_repeated_prime_bound {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {x t : ℝ}
    (hx : 2 ≤ x) (htl : x ^ (11 / 20 + ε) ≤ t) (htu : t ≤ 2 * x ^ (11 / 20 + ε)) :
    ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card ≤
      4 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
  have h₁ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card ≤ 4 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
    sorry
  exact h₁

/-- LEAF: repeated prime factors in the deleted part of k_m, P0069 page 53. MEDIUM, for Open
Math OS: on J, the terms with p^2 ∣ m for a prime p ≥ m^c1, weighted by log m over log Y, have mass
at most C Y^(1-c1). Bounded weight, at most (1/c1)^3 triples, and at most 2Y Σ_{p ≥ Y^c1} p^(-2)
plus (2Y)^(1/2) such m, with c1 about 1/8. Easier than the parent: a counting bound, no density.
Non-vacuity: m = q^2 r in J with q a prime near Y^c1. -/
theorem upper_self_scaled_deleted_repeated_prime_bound
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, x ^ (11 / 20 + ε) ≤ t →
      t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                  then 0 else 1)) : ℝ) : ℂ))‖ ≤
          C * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
  obtain ⟨K, hK0, hK⟩ := diff_bounded hε
  have hC1_pos : 0 < upperC1 ε := (upperC1_spec hε hε8).1
  have hC1_lt_one : upperC1 ε < 1 := (upperC1_spec hε hε8).2
  have hK_val : K = (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by
    norm_num [diff_bounded] at hK0 hK ⊢ <;>
    (try contradiction) <;>
    (try linarith) <;>
    (try simp_all) <;>
    (try norm_num) <;>
    (try aesop)
  use max (max K 2) (4 * K + 3)
  intro x hx t htl htu
  have hx2 : (2 : ℝ) ≤ x := by
    have h₁ : (2 : ℝ) ≤ max K 2 := by apply le_max_right
    have h₂ : (max K 2 : ℝ) ≤ max (max K 2) (4 * (1 + 18 + 18 ^ 2 + 18 ^ 3)) := by apply le_max_left
    linarith
  have hx0 : 0 < x := by linarith
  have hY : x ^ (11 / 20 + ε) ≥ 2 := by
    have h₁ : (1 : ℝ) ≤ x := by linarith
    have h₂ : x ^ (11 / 20 + ε) ≥ x ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · linarith
      · norm_num
        <;> linarith
    have h₃ : x ^ (1 / 2 : ℝ) ≥ 2 := by
      have h₄ : Real.sqrt x ≥ 2 := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      have h₅ : x ^ (1 / 2 : ℝ) = Real.sqrt x := by
        rw [Real.sqrt_eq_rpow]
        <;> norm_num
      rw [h₅] at h₄
      linarith
    linarith
  have hlogY_pos : 0 < Real.log (x ^ (11 / 20 + ε)) := Real.log_pos (by linarith)
  have hlogY : Real.log (x ^ (11 / 20 + ε)) = (11 / 20 + ε) * Real.log x := by
    rw [Real.log_rpow (by positivity)]
    <;> ring_nf
  have hsum_bound : ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
          ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
            (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
              then 0 else 1)) : ℝ) : ℂ))‖ ≤
      (4 * (1 + 18 + 18 ^ 2 + 18 ^ 3) : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
  have h₁ : ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
          ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
            (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
              then 0 else 1)) : ℝ) : ℂ))‖ ≤
      ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        |(Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
          ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
            (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
              then 0 else 1)) : ℝ)| := by
    calc
      ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                  then 0 else 1)) : ℝ) : ℂ))‖ =
          ‖(∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
                ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                  (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                    then 0 else 1)) : ℝ) : ℂ)))‖ := by rfl
      _ ≤ ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ‖((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                  then 0 else 1)) : ℝ) : ℂ)‖ := by
        apply Finset.norm_sum_le
      _ = ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          |(Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
            ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
              (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                then 0 else 1)) : ℝ| := by
        apply Finset.sum_congr rfl
        intro m _
        simp [Complex.norm_eq_abs, Complex.abs_ofReal]
  have h₂ : ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      |(Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
        ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
          (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
            then 0 else 1)) : ℝ| ≤
      (4 * (1 + 18 + 18 ^ 2 + 18 ^ 3) : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
  have h₃ : ∀ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      |(Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
        ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
          (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
            then 0 else 1)) : ℝ| ≤
      2 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by
    intro m hm
    have h₄ : (m : ℝ) ≤ t := by
      simp only [Finset.mem_filter, Finset.mem_setOf_eq] at hm
      exact hm.2
    have h₅ : (m : ℝ) ≥ x ^ (11 / 20 + ε) := by
      have h₅₁ : m ∈ rightInterval ε x := by
        simp only [Finset.mem_filter, Finset.mem_setOf_eq] at hm
        exact hm.1
      have h₅₂ : m ∈ Finset.Ioc (⌊x ^ (11 / 20 + ε)⌋₊) (⌊2 * x ^ (11 / 20 + ε)⌋₊) := by
        simpa [rightInterval] using h₅₁
      have h₅₃ : (⌊x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast Finset.mem_Ioc.mp h₅₂ |>.1
      have h₅₄ : (m : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by
        exact_mod_cast Finset.mem_Ioc.mp h₅₂ |>.2
      have h₅₅ : x ^ (11 / 20 + ε) < (m : ℝ) := by
        have h₅₆ := Nat.lt_floor_add_one (x ^ (11 / 20 + ε))
        linarith
      linarith
    have h₆ : 0 < Real.log (x ^ (11 / 20 + ε)) := Real.log_pos (by linarith)
    have h₇ : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by
      have h₇₁ : (1 : ℝ) ≤ (m : ℝ) := by
        have h₇₂ : x ^ (11 / 20 + ε) ≥ 2 := by linarith
        linarith
      linarith)
    have h₈ : Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) ≤ 2 := by
      have h₈₁ : Real.log (m : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) := by
        apply Real.log_le_log
        · linarith
        · have h₈₂ : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
            have h₈₃ : (m : ℝ) ≤ t := h₄
            linarith
          linarith
      have h₈₄ : Real.log (2 * x ^ (11 / 20 + ε)) = Real.log 2 + Real.log (x ^ (11 / 20 + ε)) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      have h₈₅ : Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) ≤ (Real.log 2 + Real.log (x ^ (11 / 20 + ε))) / Real.log (x ^ (11 / 20 + ε)) := by
        gcongr
      have h₈₆ : (Real.log 2 + Real.log (x ^ (11 / 20 + ε))) / Real.log (x ^ (11 / 20 + ε)) = Real.log 2 / Real.log (x ^ (11 / 20 + ε)) + 1 := by
        field_simp [h₆.ne']
        <;> ring
      have h₈₇ : Real.log 2 / Real.log (x ^ (11 / 20 + ε)) + 1 ≤ 2 := by
        have h₈₈ : Real.log 2 ≤ Real.log (x ^ (11 / 20 + ε)) := by
          apply Real.log_le_log
          · positivity
          · have h₈₉ : (2 : ℝ) ≤ x ^ (11 / 20 + ε) := by linarith
            linarith
        have h₈₉ : 0 < Real.log (x ^ (11 / 20 + ε)) := by positivity
        have h₉₀ : Real.log 2 / Real.log (x ^ (11 / 20 + ε)) ≤ 1 := by
          rw [div_le_iff h₈₉]
          linarith
        linarith
      linarith
    have h₉ : 0 ≤ Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) := by positivity
    have h₁₀ : 0 ≤ (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) := (hK m).1
    have h₁₁ : (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) ≤ (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := (hK m).2
    have h₁₂ : (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε then (0 : ℝ) else 1) = 0 ∨ (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε then (0 : ℝ) else 1) = 1 := by
      by_cases h : ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])
    cases h₁₂ with
    | inl h₁₂ =>
      rw [h₁₂]
      simp [abs_of_nonneg, h₉, h₁₀]
      <;> norm_num
    | inr h₁₂ =>
      rw [h₁₂]
      have h₁₃ : 0 ≤ Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) := by positivity
      have h₁₄ : Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) ≤ 2 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by
        calc
          Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) ≤ 2 * (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) := by
            gcongr
          _ ≤ 2 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by
            gcongr
      rw [abs_of_nonneg (by positivity)]
      linarith
  have h₄ : ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      |(Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
        ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
          (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
            then 0 else 1)) : ℝ| ≤
      ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (2 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ)) := by
    apply Finset.sum_le_sum
    intro m hm
    exact h₃ m hm
  have h₅ : ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      (2 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ)) = (2 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ)) * ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).card := by
    simp [Finset.sum_const, nsmul_eq_mul]
    <;> ring
  have h₆ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).card ≤ ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card + ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ¬(∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε))).card := by
    have h₆₁ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)) ⊆ ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)) ∪ ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ¬(∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε))) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_filter] at hm ⊢
      by_cases h₆₂ : ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε
      · exact Or.inr ⟨by tauto, by tauto⟩
      · exact Or.inl ⟨by tauto, by tauto⟩
    have h₆₃ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).card ≤ (((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)) ∪ ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ¬(∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)))).card := Finset.card_le_card h₆₁
    have h₆₄ : (((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)) ∪ ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ¬(∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)))).card ≤ ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card + ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ¬(∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε))).card := by
      calc
        _ ≤ ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card + ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ¬(∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε))).card := by
          apply Finset.card_union_le
        _ = _ := by rfl
    linarith
  have h₇ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ¬(∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε))).card = 0 := by
    have h₇₁ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ¬(∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε))) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro m hm
      simp only [Finset.mem_filter] at hm ⊢
      by_cases h₇₂ : ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε
      · exfalso
        simp_all
      · simp_all
    rw [h₇₁]
    simp
  have h₈ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).card ≤ ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card := by
    linarith
  have h₉ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card ≤ 4 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
    have h₉₁ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card ≤ 4 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
      have h₉₂ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card ≤ 4 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
        have h₉₃ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card ≤ 4 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
          -- Use the card_repeated_prime_bound lemma
          have h₉₄ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card ≤ 4 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
            -- This is exactly the statement of card_repeated_prime_bound
            have h₉₅ : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card ≤ 4 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
              apply card_repeated_prime_bound hε hε8 hx2 htl htu
            exact h₉₅
          exact h₉₄
        exact h₉₃
      exact h₉₂
    exact h₉₁
  calc
    ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      |(Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
        ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
          (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
            then 0 else 1)) : ℝ| ≤ ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (2 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ)) := h₄
    _ = (2 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ)) * ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).card := by rw [h₅]
    _ ≤ (2 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ)) * ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t ∧ ∃ p ∈ m.primeFactors, p ^ 2 ∣ m ∧ (p : ℝ) ≥ (m : ℝ) ^ upperC1 ε)).card := by
      gcongr
    _ ≤ (2 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ)) * (4 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε))) := by
      gcongr
    _ = (4 * (1 + 18 + 18 ^ 2 + 18 ^ 3) : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
      ring_nf
      <;> field_simp [Real.sqrt_eq_rpow, mul_comm]
      <;> ring_nf
      <;> norm_num
      <;> linarith [hC1_pos, hC1_lt_one]
  linarith
  have h_final : ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
          ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
            (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
              then 0 else 1)) : ℝ) : ℂ))‖ ≤
      (max (max K 2) (4 * K + 3) : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
    have h₁ : ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
          ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
            (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
              then 0 else 1)) : ℝ) : ℂ))‖ ≤
      (4 * K : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := by
      exact hsum_bound
    have h₂ : (x : ℝ) ≥ 2 := by exact_mod_cast hx2
    have h₃ : (x ^ (11 / 20 + ε) : ℝ) ≥ 2 := by
      have h₄ : (x : ℝ) ≥ 2 := by exact_mod_cast hx2
      have h₅ : (x : ℝ) ^ (11 / 20 + ε) ≥ (x : ℝ) ^ (1 / 2 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · linarith
        · norm_num <;> linarith
      have h₆ : (x : ℝ) ^ (1 / 2 : ℝ) ≥ 2 := by
        have h₇ : Real.sqrt x ≥ 2 := by
          apply Real.le_sqrt_of_sq_le
          nlinarith
        have h₈ : (x : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt x := by
          rw [Real.sqrt_eq_rpow]
          <;> norm_num
        rw [h₈] at h₇
        linarith
      linarith
    have h₄ : Real.sqrt (2 * x ^ (11 / 20 + ε)) ≤ (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
      have h₅ : 0 < x ^ (11 / 20 + ε) := by positivity
      have h₆ : Real.sqrt (2 * x ^ (11 / 20 + ε)) = Real.sqrt 2 * Real.sqrt (x ^ (11 / 20 + ε)) := by
        rw [Real.sqrt_mul (by positivity)]
        <;> ring_nf
      rw [h₆]
      have h₇ : Real.sqrt (x ^ (11 / 20 + ε)) = (x ^ (11 / 20 + ε)) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        <;> norm_num
      rw [h₇]
      have h₈ : (x ^ (11 / 20 + ε) : ℝ) ^ (1 / 2 : ℝ) ≤ (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · linarith
        · have h₉ : (1 / 2 : ℝ) ≤ 1 - upperC1 ε := by
            have h₁₀ : upperC1 ε < 1 := hC1_lt_one
            have h₁₁ : 0 < upperC1 ε := hC1_pos
            have h₁₂ : upperC1 ε ≤ 1 / 2 := by
              have h₁₃ : upperC1 ε = (1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5)) : ℝ) / 15 - ε := by rfl
              rw [h₁₃]
              norm_num at hε8 ⊢
              <;> linarith
            linarith
          linarith
      have h₉ : Real.sqrt 2 * (x ^ (11 / 20 + ε) : ℝ) ^ (1 / 2 : ℝ) ≤ Real.sqrt 2 * (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) := by
        gcongr
      have h₁₀ : Real.sqrt 2 * (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) ≤ (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) := by
        have h₁₁ : Real.sqrt 2 ≤ (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) / (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) := by
          have h₁₂ : (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) ≥ 1 := by
            apply Real.one_le_rpow
            · have h₁₃ : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := by linarith
              linarith
            · linarith
          have h₁₃ : Real.sqrt 2 ≤ 2 := by norm_num [Real.sqrt_le_iff]
          have h₁₄ : (2 : ℝ) ≤ (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) := by
            have h₁₅ : (x ^ (11 / 20 + ε) : ℝ) ≥ 2 := by linarith
            have h₁₆ : (1 - upperC1 ε : ℝ) ≥ 1 / 2 := by
              have h₁₇ : upperC1 ε ≤ 1 / 2 := by
                have h₁₈ : upperC1 ε = (1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5)) : ℝ) / 15 - ε := by rfl
                rw [h₁₈]
                norm_num at hε8 ⊢
                <;> linarith
              linarith
            have h₁₉ : (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) ≥ (x ^ (11 / 20 + ε) : ℝ) ^ (1 / 2 : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_le
              · linarith
              · linarith
            have h₂₀ : (x ^ (11 / 20 + ε) : ℝ) ^ (1 / 2 : ℝ) ≥ 2 := by
              have h₂₁ : Real.sqrt (x ^ (11 / 20 + ε)) ≥ 2 := by
                apply Real.le_sqrt_of_sq_le
                nlinarith
              have h₂₂ : (x ^ (11 / 20 + ε) : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (x ^ (11 / 20 + ε)) := by
                rw [Real.sqrt_eq_rpow]
                <;> norm_num
              rw [h₂₂] at *
              linarith
            linarith
          have h₂₁ : Real.sqrt 2 ≤ (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) := by linarith
          have h₂₂ : Real.sqrt 2 ≤ (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) / (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) := by
            have h₂₃ : (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) > 0 := by positivity
            have h₂₄ : (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) / (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) = 1 := by
              field_simp [h₂₃.ne']
            have h₂₅ : Real.sqrt 2 ≤ 1 := by
              norm_num [Real.sqrt_le_iff]
              <;> linarith
            linarith
          linarith
        have h₂₃ : Real.sqrt 2 * (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) ≤ (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) := by
          have h₂₄ : Real.sqrt 2 ≤ 1 := by
            norm_num [Real.sqrt_le_iff]
            <;> linarith
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
        linarith
      have h₁₁ : Real.sqrt 2 * (x ^ (11 / 20 + ε) : ℝ) ^ (1 / 2 : ℝ) ≤ (x ^ (11 / 20 + ε) : ℝ) ^ (1 - upperC1 ε) := by
        linarith
      linarith
    have h₅ : (4 * K : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) ≤ (max (max K 2) (4 * K + 3) : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
      have h₆ : (2 : ℝ) * Real.sqrt (2 * x ^ (11 / 20 + ε)) ≤ 3 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
        have h₇ : Real.sqrt (2 * x ^ (11 / 20 + ε)) ≤ (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := h₄
        nlinarith [Real.sqrt_nonneg (2 * x ^ (11 / 20 + ε)), Real.sqrt_nonneg 2]
      have h₇ : (4 * K : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) ≤ (4 * K : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 3 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
        linarith
      have h₈ : (4 * K : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 3 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) = (4 * K + 3 : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by ring
      have h₉ : (4 * K + 3 : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) ≤ (max (max K 2) (4 * K + 3) : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
        have h₁₀ : (4 * K + 3 : ℝ) ≤ max (max K 2) (4 * K + 3) := by
          apply le_max_right
        have h₁₁ : 0 ≤ (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by positivity
        nlinarith
      linarith
    have h₆ : (max (max K 2) (4 * K + 3) : ℝ) = (max (max K 2) (4 * (1 + 18 + 18 ^ 2 + 18 ^ 3)) : ℝ) := by
      norm_num [hK_val] at * <;>
      (try simp_all) <;>
      (try norm_num) <;>\
      (try linarith)
    have h₇ : ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
          ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
            (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
              then 0 else 1)) : ℝ) : ℂ))‖ ≤
      (max (max K 2) (4 * (1 + 18 + 18 ^ 2 + 18 ^ 3)) : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
      calc
        _ ≤ (4 * K : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) + 2 * Real.sqrt (2 * x ^ (11 / 20 + ε)) := h₁
        _ ≤ (max (max K 2) (4 * K + 3) : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := h₅
        _ = (max (max K 2) (4 * (1 + 18 + 18 ^ 2 + 18 ^ 3)) : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
          norm_num [hK_val] at * <;>
          (try simp_all) <;>
          (try norm_num) <;>\
          (try linarith)
    exact h₇
  exact h_final

/-- LEAF: the main part of the deleted density of P0069 page 53, the set E not covered by
Lemma 33. HARD, for Codex: k_m minus its kept part at the self scale, restricted to m with no
repeated prime factor p ≥ m^c1 and weighted by log m over log Y, has on each segment from Y to t,
Y ≤ t ≤ 2Y, mass upperDeletedIntegral over log Y per element up to C Y (log x)^(-A). The prime
number theorem with de la Vallee Poussin error for p1, p2, p3 and the Buchstab asymptotic for the
cofactor n4, then partial summation to the triple integral over E. Easier than the parent: the
repeated prime terms are removed. Non-vacuity: at t = 2Y the segment is the whole interval. -/
theorem upper_self_scaled_deleted_squarefree_centred_prefix_bound
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, x ^ (11 / 20 + ε) ≤ t →
      t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                  then 1 else 0)) : ℝ) : ℂ) -
            ((upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- Proved: the power saving Y^(1-c1) beats every power of log. -/
theorem upper_self_scaled_power_saving {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    (A : ℝ) (hA : 0 < A) (C1 : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      C1 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) ≤ C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  set s : ℝ := 11 / 20 + ε with hs
  set c : ℝ := upperC1 ε with hc
  have hc0 : 0 < c := by rw [hc]; unfold upperC1; norm_num; linarith
  have hs0 : 0 < s := by rw [hs]; linarith
  have hlo := (isLittleO_log_rpow_rpow_atTop A (mul_pos hs0 hc0)).bound (c := 1) one_pos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hlo
  refine ⟨max (max N 2) |C1|, fun x hx => ?_⟩
  have hx2 : (2:ℝ) ≤ x := le_trans (le_trans (le_max_right N 2) (le_max_left _ _)) hx
  have hxN : N ≤ x := le_trans (le_trans (le_max_left N 2) (le_max_left _ _)) hx
  have hC1 : |C1| ≤ max (max N 2) |C1| := le_max_right _ _
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hb := hN x hxN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hb
  have hlA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hl0 A
  have key : x ^ (-(s * c)) ≤ Real.log x ^ (-A) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_neg hl0.le]
    exact inv_anti₀ hlA hb
  have hpow : (x ^ s) ^ (1 - c) = x ^ s * x ^ (-(s * c)) := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; ring_nf
  have hxs : 0 ≤ x ^ s := Real.rpow_nonneg hx0.le _
  rw [hpow]
  calc C1 * (x ^ s * x ^ (-(s * c))) ≤ |C1| * (x ^ s * x ^ (-(s * c))) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C1| * (x ^ s * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hxs) (abs_nonneg _)
    _ ≤ max (max N 2) |C1| * (x ^ s * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_right hC1 (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- The statement of `upper_self_scaled_deleted_centred_prefix_bound` of the imported file,
verbatim, assembled from the two leaves and the proved power saving lemma: the deleted part splits
as the repeated prime part plus the main part, and the triangle inequality adds the bounds. -/
theorem upper_self_scaled_deleted_centred_prefix_bound_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, x ^ (11 / 20 + ε) ≤ t →
      t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) : ℝ) : ℂ) -
            ((upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := upper_self_scaled_deleted_repeated_prime_bound hε hε8
  obtain ⟨C2, hC2⟩ :=
    upper_self_scaled_deleted_squarefree_centred_prefix_bound h4 h9 hω hz hε hε8 A hA
  obtain ⟨C3, hC3⟩ := upper_self_scaled_power_saving hε hε8 A hA C1
  refine ⟨max (max (max C1 C2) C3) 1 + |C2| + |C3|, fun x hx t htl htu => ?_⟩
  have hab : 0 ≤ |C2| + |C3| := by positivity
  have hmx : max (max (max C1 C2) C3) 1 ≤ x := by linarith
  have hx1 : C1 ≤ x := le_trans (le_trans (le_trans (le_max_left C1 C2) (le_max_left _ C3))
    (le_max_left _ 1)) hmx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_trans (le_max_right C1 C2) (le_max_left _ C3))
    (le_max_left _ 1)) hmx
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_right _ C3) (le_max_left _ 1)) hmx
  have hxo : (1 : ℝ) ≤ x := le_trans (le_max_right _ 1) hmx
  set L : ℝ := Real.log (x ^ (11 / 20 + ε)) with hL
  set d : ℝ := upperDeletedIntegral ω ε with hd
  set S := (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) with hS
  have hsum : ∀ m ∈ S, ((((Real.log (m : ℝ) / L *
              (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) : ℝ) : ℂ) - ((d : ℝ) : ℂ) / (L : ℂ))) =
      ((((Real.log (m : ℝ) / L *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                  then 0 else 1)) : ℝ) : ℂ))
      + (((Real.log (m : ℝ) / L *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                  then 1 else 0)) : ℝ) : ℂ) - ((d : ℝ) : ℂ) / (L : ℂ))) := by
    intro m _
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib]
  have hYL : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (Real.log_nonneg hxo) _)
  refine le_trans (norm_add_le _ _) ?_
  have e1 := hC1 x hx1 t htl htu
  have e2 := hC2 x hx2 t htl htu
  have e3 := hC3 x hx3
  have hc : C3 + C2 ≤ max (max (max C1 C2) C3) 1 + |C2| + |C3| := by
    have : (0:ℝ) ≤ max (max (max C1 C2) C3) 1 := le_trans (by norm_num) (le_max_right _ 1)
    linarith [le_abs_self C2, le_abs_self C3]
  calc _ ≤ C3 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) +
        C2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := add_le_add (le_trans e1 e3) e2
    _ = (C3 + C2) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
    _ ≤ (max (max (max C1 C2) C3) 1 + |C2| + |C3|) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_right hc hYL
    _ = _ := by ring

end LeanLab.BHP1997.Upper312Route
