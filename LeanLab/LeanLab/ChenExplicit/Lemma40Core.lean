/-
AI wrote this Lean code. CODEX task44.
BJS arXiv 2207.09452 v6, Lemma 40, pages 38 and 39.
This proves the arithmetic core after the paper bounds q2 below by 2 ell minus 1.
The prime ordering and oddness are not redefined or assumed away.
They enter through the explicit lower bounds in lemma40_core.
-/
import Mathlib

open Finset

namespace LeanLab.ChenExplicit.Lemma40Core

/-- Reciprocal products of initial segments of a real sequence. -/
noncomputable def reciprocalPrefixes (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range n, (∏ i ∈ range (j + 1), a i)⁻¹

lemma prefix_ge_head {n j : ℕ} {a : ℕ → ℝ} (hj : j < n)
    (ha : ∀ i < n, 1 ≤ a i) : a 0 ≤ ∏ i ∈ range (j + 1), a i := by
  have h0 : 0 ≤ a 0 := le_trans (by norm_num) (ha 0 (by omega))
  rw [prod_range_succ']
  have ht : 1 ≤ ∏ i ∈ range j, a (i + 1) := by
    apply one_le_prod₀
    intro i hi
    exact ha (i + 1) (by have := mem_range.mp hi; omega)
  simpa using mul_le_mul_of_nonneg_right ht h0

/-- The paper bounds each term by the reciprocal of its first denominator. -/
theorem reciprocalPrefixes_le {n : ℕ} {a : ℕ → ℝ}
    (ha : ∀ i < n, 1 ≤ a i) (hhead : (n : ℝ) ≤ a 0) : reciprocalPrefixes n a ≤ 1 := by
  by_cases hn : n = 0
  · simp [reciprocalPrefixes, hn]
  have h0 : 0 < a 0 := lt_of_lt_of_le (by norm_num) (ha 0 (by omega))
  have hs : reciprocalPrefixes n a ≤ (n : ℝ) / a 0 := by
    unfold reciprocalPrefixes
    calc (∑ j ∈ range n, (∏ i ∈ range (j + 1), a i)⁻¹)
        ≤ ∑ _j ∈ range n, (a 0)⁻¹ := by
          apply sum_le_sum
          intro j hj
          simpa only [one_div] using one_div_le_one_div_of_le h0 (prefix_ge_head (mem_range.mp hj) ha)
      _ = (n : ℝ) / a 0 := by simp [div_eq_mul_inv, nsmul_eq_mul]
  exact hs.trans ((div_le_one h0).mpr hhead)

/-- Lemma 40 after the lower bounds on its odd prime factors have been established. -/
theorem lemma40_core {ell : ℕ} (hell : 2 ≤ ell) (q : ℕ → ℕ)
    (hq : ∀ i < ell - 1, 3 ≤ q (i + 2))
    (hhead : 2 * (ell : ℝ) - 1 ≤ q 2) :
    reciprocalPrefixes (ell - 1) (fun i => (q (i + 2) : ℝ) - 2) ≤ 1 := by
  apply reciprocalPrefixes_le
  · intro i hi
    have h := hq i hi
    have h' : (3 : ℝ) ≤ q (i + 2) := by exact_mod_cast h
    linarith
  · simp only [zero_add]
    rw [Nat.cast_sub (by omega : 1 ≤ ell)]
    norm_num
    have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
    linarith

/-- Concrete instance: ell equal 3 and q2, q3 equal 5, 3. -/
example : reciprocalPrefixes 2 (fun i => if i = 0 then 3 else 1) ≤ 1 := by
  apply reciprocalPrefixes_le
  · intro i _; split_ifs <;> norm_num
  · norm_num

#print axioms prefix_ge_head
#print axioms reciprocalPrefixes_le
#print axioms lemma40_core

end LeanLab.ChenExplicit.Lemma40Core
