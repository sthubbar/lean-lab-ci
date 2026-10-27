/-
P0087 Akeno 2026 equation 44 on page 31 and Appendix 5.1 page 36.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.Thm12Numerics

namespace LeanLab.Akeno2026.Thm12Numerics
open Finset

/-- Count the coordinates where Kuhn's weight contributes one half. -/
theorem kuhnG_eq_count {r : ℕ} (t : ℝ) (u : Fin r → ℝ) :
    kuhnG t u = max 0 (1 -
      ((univ.filter (fun i => 0 ≤ u i ∧ u i ≤ 1 / t)).card : ℝ) * (1 / 2)) := by
  classical
  unfold kuhnG
  congr 2
  unfold kuhnF
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul, add_zero]

/-- Equation 44 for ordered nonnegative coordinates, without needing the simplex constraint. -/
theorem kuhnG_ordered (r : ℕ) (t : ℝ) (u : Fin (r + 2) → ℝ)
    (hm : Monotone u) (hu : ∀ i, 0 ≤ u i) :
    kuhnG t u =
      if 1 / t < u ⟨0, by omega⟩ then 1
      else if 1 / t < u ⟨1, by omega⟩ then 1 / 2 else 0 := by
  classical
  let i0 : Fin (r + 2) := ⟨0, by omega⟩
  let i1 : Fin (r + 2) := ⟨1, by omega⟩
  change kuhnG t u = if 1 / t < u i0 then 1 else if 1 / t < u i1 then 1 / 2 else 0
  by_cases h0 : 1 / t < u i0
  · rw [ite_eq_left h0]
    have hf : ∀ i, kuhnF t (u i) = 0 := by
      intro i
      have hle : i0 ≤ i := by change 0 ≤ i.val; omega
      have hi : 1 / t < u i := h0.trans_le (hm hle)
      unfold kuhnF
      exact ite_eq_right (fun h => (not_le.mpr hi) h.2)
    unfold kuhnG
    simp_rw [hf]
    norm_num
  · rw [ite_eq_right h0]
    have h0' : u i0 ≤ 1 / t := le_of_not_gt h0
    by_cases h1 : 1 / t < u i1
    · rw [ite_eq_left h1]
      have hf : ∀ i, kuhnF t (u i) = if i = i0 then 1 / 2 else 0 := by
        intro i
        by_cases hi : i = i0
        · subst i
          unfold kuhnF
          rw [ite_eq_left (show 0 ≤ u i0 ∧ u i0 ≤ 1 / t from ⟨hu i0, h0'⟩)]
          simp
        · have hv : i.val ≠ 0 := by
            intro he
            apply hi
            apply Fin.ext
            exact he
          have hle : i1 ≤ i := by change 1 ≤ i.val; omega
          have hlarge : 1 / t < u i := h1.trans_le (hm hle)
          simp only [kuhnF, ite_eq_right (show ¬ (0 ≤ u i ∧ u i ≤ 1 / t) from
            fun h => (not_le.mpr hlarge) h.2), ite_eq_right hi]
      unfold kuhnG
      simp_rw [hf]
      norm_num
    · rw [ite_eq_right h1]
      have h1' : u i1 ≤ 1 / t := le_of_not_gt h1
      have hne : i0 ≠ i1 := by
        intro he
        have h := congrArg Fin.val he
        norm_num [i0, i1] at h
      have hf0 : kuhnF t (u i0) = 1 / 2 := by
        unfold kuhnF
        exact ite_eq_left ⟨hu i0, h0'⟩
      have hf1 : kuhnF t (u i1) = 1 / 2 := by
        unfold kuhnF
        exact ite_eq_left ⟨hu i1, h1'⟩
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg
        (show ({i0, i1} : Finset (Fin (r + 2))) ⊆ univ from subset_univ _)
        (fun i _ _ => kuhnF_nonneg t (u i))
      have hone : (1 : ℝ) ≤ ∑ i, kuhnF t (u i) := by
        norm_num [Finset.sum_pair hne, hf0, hf1] at hsum
        exact hsum
      unfold kuhnG
      exact max_eq_left (by linarith)

end LeanLab.Akeno2026.Thm12Numerics
