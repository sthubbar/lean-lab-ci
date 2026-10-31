/-
AI wrote this Lean code. Codex task69, 2026-10-25.
Elementary lower bounds for the local factors of the singular series.
Source: the singular series cited on page 357 of Zinoviev 1997.
These estimates do not assert the Euler factorization of that series.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.Arith

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology

/-- The worst local factor at an odd integer 2k plus 1. -/
noncomputable def worstFactor (k : ℕ) : ℝ := 1 - 1 / (2 * (k : ℝ)) ^ 2

/-- A telescoping majorant for the tail of reciprocal even squares. -/
theorem evenSquare_le_telescoping (k : ℕ) (hk : 2 ≤ k) :
    1 / (2 * (k : ℝ)) ^ 2 ≤
      (1 / (4 * ((k : ℝ) - 1)) - 1 / (4 * k)) := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  field_simp
  nlinarith

/-- Sum over k from 3 through M is at most one eighth. -/
theorem evenSquare_tail (M : ℕ) :
    ∑ k ∈ Finset.Icc 3 M, (1 / (2 * (k : ℝ)) ^ 2) ≤ 1 / 8 := by
  have h : ∀ n : ℕ, ∑ k ∈ Finset.Icc 3 (n + 2), (1 / (2 * (k : ℝ)) ^ 2) ≤
      1 / 8 - 1 / (4 * ((n : ℝ) + 2)) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        Finset.sum_Icc_succ_top (by omega)]
      have hk := evenSquare_le_telescoping (n + 3) (by omega)
      push_cast at hk ⊢
      have heq : (n : ℝ) + 3 - 1 = n + 2 := by ring
      simp only [heq] at hk
      convert (add_le_add ih hk) using 1 <;> ring
  rcases Nat.lt_or_ge M 3 with hm | hm
  · have : Finset.Icc 3 M = ∅ := Finset.Icc_eq_empty_of_lt hm
    norm_num [this]
  · have hh := h (M - 2)
    have he : ((M - 2 : ℕ) : ℝ) + 2 = M := by
      rw [Nat.cast_sub (by omega : 2 ≤ M)]
      push_cast
      ring
    rw [Nat.sub_add_cancel (by omega : 2 ≤ M), he] at hh
    have : (0 : ℝ) ≤ 1 / (4 * (M : ℝ)) := by positivity
    linarith

/-- The sum of reciprocal even squares after the first factor is at most 3/16. -/
theorem evenSquare_sum (M : ℕ) :
    ∑ k ∈ Finset.Icc 2 M, (1 / (2 * (k : ℝ)) ^ 2) ≤ 3 / 16 := by
  by_cases hm : 2 ≤ M
  · have he : Finset.Icc 2 M = insert 2 (Finset.Icc 3 M) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [he, Finset.sum_insert (by simp)]
    have := evenSquare_tail M
    norm_num at this ⊢
    linarith
  · have : Finset.Icc 2 M = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    norm_num [this]

/-- The finite product after k equals 1 is at least thirteen sixteenths. -/
theorem worstFactor_tail (M : ℕ) :
    (13 : ℝ) / 16 ≤ ∏ k ∈ Finset.Icc 2 M, worstFactor k := by
  have hprod : ∀ s : Finset ℕ, (∀ k ∈ s, 2 ≤ k) →
      1 - ∑ k ∈ s, (1 / (2 * (k : ℝ)) ^ 2) ≤ ∏ k ∈ s, worstFactor k := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      intro hs
      have ha2 := hs a (by simp)
      have hs2 : ∀ k ∈ s, 2 ≤ k := fun k hk => hs k (by simp [hk])
      have har : (2 : ℝ) ≤ a := by exact_mod_cast ha2
      have hv : 0 ≤ worstFactor a := by
        unfold worstFactor
        have hd : (1 : ℝ) ≤ (2 * (a : ℝ)) ^ 2 := by nlinarith
        have : 1 / (2 * (a : ℝ)) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hd
        linarith
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hh := mul_le_mul_of_nonneg_left (ih hs2) hv
      have hsum : 0 ≤ ∑ k ∈ s, (1 / (2 * (k : ℝ)) ^ 2) := by positivity
      have hcross := mul_nonneg (show 0 ≤ 1 / (2 * (a : ℝ)) ^ 2 by positivity) hsum
      simp only [worstFactor] at *
      nlinarith
  have hh := hprod (Finset.Icc 2 M) (fun k hk => (Finset.mem_Icc.mp hk).1)
  have hs := evenSquare_sum M
  linarith

/-- Twice the complete worst factor product is at least 39/32. -/
theorem worstFactor_product (M : ℕ) (hM : 1 ≤ M) :
    (39 : ℝ) / 32 ≤ 2 * ∏ k ∈ Finset.Icc 1 M, worstFactor k := by
  have he : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [he, Finset.prod_insert (by simp)]
  have := worstFactor_tail M
  norm_num [worstFactor] at this ⊢
  linarith

end LeanLab.Zinoviev1997
