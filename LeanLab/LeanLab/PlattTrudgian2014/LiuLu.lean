/-
Platt, Trudgian 2014, P0024, arXiv 1404.5669v2, page 3: "Liu and Lü used D = 11 to show
that C₃ ≥ 2.8096". Here: the sum 2 Σ k(d) H(d; N, K) ε(d)^{-K} over the d ≤ 11 for which
2 is a primitive root, d = 1, 3, 5, 11, is at least 2.8096 for every K ≥ 6 and every N,
with minimum 2.80975278125 at K = 6. The d = 7 term, ε(7) = 3, is nonnegative and left out,
as in Heath-Brown and Puchta's method; d = 9 has k(9) = 0.
k(3) = 1, k(5) = 1/3, k(11) = 1/9.

AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.PlattTrudgian2014.Section2

namespace LeanLab.PlattTrudgian2014.Section2

open Finset

theorem primRoot_11 : (Function.Injective fun j : Fin 10 => (2 : ZMod 11) ^ ((j : ℕ) + 1)) ∧
    (univ.image fun j : Fin 10 => (2 : ZMod 11) ^ ((j : ℕ) + 1)) = univ.erase 0 := by
  constructor
  · decide
  · decide

theorem H11_ratio (K : ℕ) (c : ZMod 11) :
    (H 11 10 K c : ℝ) / 10 ^ K = 1 / 11 * (1 + (-1) ^ K * (if c = 0 then 10 else -1) / 10 ^ K) := by
  have h := hbp_formula 11 K primRoot_11.1 primRoot_11.2 c
  have h' : (11 : ℝ) * H 11 10 K c = 10 ^ K + (-1) ^ K * (if c = 0 then 10 else -1) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    split_ifs at this ⊢ <;> norm_num at this ⊢ <;> linarith
  field_simp
  linarith

/-- The D = 11 sum over d = 1, 3, 5, 11, with N given by its residues mod 3, 5, 11. -/
noncomputable def C3sum11 (K : ℕ) (a : ZMod 3) (b : ZMod 5) (c : ZMod 11) : ℝ :=
  2 * (1 + (H 3 2 K a : ℝ) / 2 ^ K + 1 / 3 * ((H 5 4 K b : ℝ) / 4 ^ K)
    + 1 / 9 * ((H 11 10 K c : ℝ) / 10 ^ K))

/-- Liu and Lü's C₃ ≥ 2.8096 with D = 11, for every K ≥ 6 and every N. -/
theorem liuLu_C3_D11 (K : ℕ) (hK : 6 ≤ K) (a : ZMod 3) (b : ZMod 5) (c : ZMod 11) :
    2.8096 ≤ C3sum11 K a b c := by
  unfold C3sum11
  rw [H3_ratio, H5_ratio, H11_ratio]
  have h2 : (64 : ℝ) ≤ 2 ^ K := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hK
  have h4 : (4096 : ℝ) ≤ 4 ^ K := by
    calc (4096 : ℝ) = 4 ^ 6 := by norm_num
      _ ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hK
  have h10 : (1000000 : ℝ) ≤ 10 ^ K := by
    calc (1000000 : ℝ) = 10 ^ 6 := by norm_num
      _ ≤ 10 ^ K := pow_le_pow_right₀ (by norm_num) hK
  rcases Nat.even_or_odd K with he | ho
  · rw [he.neg_one_pow]
    have h3 : -1 / 64 ≤ (if a = 0 then (2 : ℝ) else -1) / 2 ^ K := by
      split_ifs
      · exact le_trans (b := 0) (by norm_num) (div_nonneg (by norm_num) (by positivity))
      · rw [le_div_iff₀ (by positivity)]; linarith
    have h5 : -1 / 4096 ≤ (if b = 0 then (4 : ℝ) else -1) / 4 ^ K := by
      split_ifs
      · exact le_trans (b := 0) (by norm_num) (div_nonneg (by norm_num) (by positivity))
      · rw [le_div_iff₀ (by positivity)]; linarith
    have h11 : -1 / 1000000 ≤ (if c = 0 then (10 : ℝ) else -1) / 10 ^ K := by
      split_ifs
      · exact le_trans (b := 0) (by norm_num) (div_nonneg (by norm_num) (by positivity))
      · rw [le_div_iff₀ (by positivity)]; linarith
    simp only [one_mul]
    nlinarith
  · have hK7 : 7 ≤ K := by
      rcases ho with ⟨m, rfl⟩; omega
    have h2' : (128 : ℝ) ≤ 2 ^ K := by
      calc (128 : ℝ) = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hK7
    have h4' : (16384 : ℝ) ≤ 4 ^ K := by
      calc (16384 : ℝ) = 4 ^ 7 := by norm_num
        _ ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hK7
    have h10' : (10000000 : ℝ) ≤ 10 ^ K := by
      calc (10000000 : ℝ) = 10 ^ 7 := by norm_num
        _ ≤ 10 ^ K := pow_le_pow_right₀ (by norm_num) hK7
    rw [ho.neg_one_pow]
    have h3 : -1 / 64 ≤ -1 * (if a = 0 then (2 : ℝ) else -1) / 2 ^ K := by
      split_ifs
      · rw [le_div_iff₀ (by positivity)]; linarith
      · exact le_trans (b := 0) (by norm_num) (div_nonneg (by norm_num) (by positivity))
    have h5 : -1 / 4096 ≤ -1 * (if b = 0 then (4 : ℝ) else -1) / 4 ^ K := by
      split_ifs
      · rw [le_div_iff₀ (by positivity)]; linarith
      · exact le_trans (b := 0) (by norm_num) (div_nonneg (by norm_num) (by positivity))
    have h11 : -1 / 1000000 ≤ -1 * (if c = 0 then (10 : ℝ) else -1) / 10 ^ K := by
      split_ifs
      · rw [le_div_iff₀ (by positivity)]; linarith
      · exact le_trans (b := 0) (by norm_num) (div_nonneg (by norm_num) (by positivity))
    nlinarith

/-- Sharp at K = 6, N ≢ 0 mod 3, 5 and 11: the sum is 2.80975278125. -/
theorem liuLu_C3_D11_K6 : C3sum11 6 1 1 1 = 2.80975278125 := by
  unfold C3sum11
  rw [H3_ratio, H5_ratio, H11_ratio]
  have h3 : (1 : ZMod 3) ≠ 0 := by decide
  have h5 : (1 : ZMod 5) ≠ 0 := by decide
  have h11 : (1 : ZMod 11) ≠ 0 := by decide
  simp only [h3, h5, h11, ite_false]
  norm_num

end LeanLab.PlattTrudgian2014.Section2
