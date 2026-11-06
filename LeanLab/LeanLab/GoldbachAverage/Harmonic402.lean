import Mathlib

/-!
The reciprocal separation sum in BHMS, arXiv 1704.06103v2 pages 16 and 17, Lemma 6.
This elementary helper treats consecutive integer shell centers uniformly in the shift.
It reuses Mathlib's harmonic number logarithmic bound.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Harmonic402
open Finset

/-- A shifted reciprocal shell sum is bounded by two harmonic prefixes.
This is the elementary harmonic step of BHMS pages 16 and 17 Lemma 6.
The explicit constant two is derived here. -/
theorem centered_reciprocal_sum (M : ℕ) (y : ℝ) :
    (∑ n ∈ range (M + 1), 1 / (1 + |(n : ℝ) - y|)) ≤
      2 * (1 + Real.log ((M : ℝ) + 1)) := by
  let f : ℕ → ℝ := fun n => 1 / (1 + |(n : ℝ) - y|)
  let b : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let B : ℝ := ∑ n ∈ range (M + 1), b n
  have hb0 (n : ℕ) : 0 ≤ b n := by dsimp [b]; positivity
  have hB0 : 0 ≤ B := sum_nonneg (fun n _ => hb0 n)
  have hrev (K : ℕ) : (∑ n ∈ range (K + 1), b (K - n)) =
      ∑ n ∈ range (K + 1), b n := by
    simpa using sum_range_reflect b (K + 1)
  have hprefix {K : ℕ} (hK : K ≤ M + 1) : (∑ n ∈ range K, b n) ≤ B :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hK) (fun n _ _ => hb0 n)
  have hsum : (∑ n ∈ range (M + 1), f n) ≤ 2 * B := by
    by_cases hy0 : y ≤ 0
    · have hp : ∀ n : ℕ, f n ≤ b n := by
        intro n
        dsimp [f, b]
        apply one_div_le_one_div_of_le (by positivity)
        linarith [le_abs_self ((n : ℝ) - y)]
      have hs := sum_le_sum (fun n (_ : n ∈ range (M + 1)) => hp n)
      change (∑ n ∈ range (M + 1), f n) ≤ 2 * B
      exact hs.trans (by dsimp [B] at *; linarith)
    by_cases hyM : (M : ℝ) ≤ y
    · have hp : ∀ n ∈ range (M + 1), f n ≤ b (M - n) := by
        intro n hn
        have hnm : n ≤ M := by have := mem_range.mp hn; omega
        dsimp [f, b]
        apply one_div_le_one_div_of_le (by positivity)
        rw [Nat.cast_sub hnm]
        linarith [neg_le_abs ((n : ℝ) - y)]
      have hs := sum_le_sum hp
      rw [hrev M] at hs
      exact hs.trans (by dsimp [B] at *; linarith)
    have hypos : 0 ≤ y := le_of_lt (lt_of_not_ge hy0)
    let K : ℕ := ⌊y⌋₊
    have hKy : (K : ℝ) ≤ y := Nat.floor_le hypos
    have hyK : y < (K : ℝ) + 1 := Nat.lt_floor_add_one y
    have hKM : K ≤ M := by
      have : (K : ℝ) ≤ M := hKy.trans (le_of_lt (lt_of_not_ge hyM))
      exact_mod_cast this
    have hl : (∑ n ∈ range (K + 1), f n) ≤ B := by
      have hp : ∀ n ∈ range (K + 1), f n ≤ b (K - n) := by
        intro n hn
        have hnK : n ≤ K := by have := mem_range.mp hn; omega
        dsimp [f, b]
        apply one_div_le_one_div_of_le (by positivity)
        rw [Nat.cast_sub hnK]
        linarith [neg_le_abs ((n : ℝ) - y)]
      have hs := sum_le_sum hp
      rw [hrev K] at hs
      exact hs.trans (hprefix (by omega))
    have hr : (∑ n ∈ Ico (K + 1) (M + 1), f n) ≤ B := by
      have hp : ∀ n ∈ Ico (K + 1) (M + 1), f n ≤ b (n - (K + 1)) := by
        intro n hn
        have hKn : K + 1 ≤ n := (mem_Ico.mp hn).1
        dsimp [f, b]
        apply one_div_le_one_div_of_le (by positivity)
        rw [Nat.cast_sub hKn, Nat.cast_add, Nat.cast_one]
        linarith [le_abs_self ((n : ℝ) - y)]
      have hs := sum_le_sum hp
      have he : (∑ n ∈ Ico (K + 1) (M + 1), b (n - (K + 1))) =
          ∑ n ∈ range (M - K), b n := by
        rw [sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_add_right, Nat.add_sub_cancel_left]
      rw [he] at hs
      exact hs.trans (hprefix (by omega))
    have hsplit := sum_Ico_eq_sub f (show K + 1 ≤ M + 1 by omega)
    linarith
  have hH : B = (harmonic (M + 1) : ℝ) := by
    simp only [B, b, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_one, one_div]
  change (∑ n ∈ range (M + 1), f n) ≤ _
  calc _ ≤ 2 * B := hsum
    _ = 2 * (harmonic (M + 1) : ℝ) := by rw [hH]
    _ ≤ 2 * (1 + Real.log ((M : ℝ) + 1)) := by
      have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (M + 1))
        (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [Nat.cast_add, Nat.cast_one] using hh

end LeanLab.GoldbachAverage.Harmonic402
