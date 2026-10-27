import LeanLab.Zhao2025.BScaledNonnegOrder
import LeanLab.Zhao2025.BNonnegOrder

/-!
Display 2.18 for the positive lambda parameters used under c0 positive.
The formula for B uses division, so its lambda equals zero boundary is excluded.
Source: Zhao 2025, Lemma 2.3, display 2.18, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- The scaling inequality of Lemma 2.3 for positive lambda and Lambda. -/
theorem lemma2_3 (t l L l0 : ℝ) (ht : 0 ≤ t) (hl : 0 < l) (hLp : 0 < L)
    (h0 : 0 ≤ l0) :
    Real.exp (-(max (L - l) 0 * t)) * B t l l0 ≤ B t L l0 := by
  by_cases h : l ≤ L
  · rw [max_eq_left (sub_nonneg.mpr h)]
    have hs := B_scaled_nonneg_order t l L l0 ht hl h0 h
    have hh := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-(L * t))).le
    have he1 : Real.exp (-(L * t)) * Real.exp (l * t) = Real.exp (-((L - l) * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have he2 : Real.exp (-(L * t)) * Real.exp (L * t) = 1 := by
      rw [← Real.exp_add, show -(L * t) + L * t = 0 by ring, Real.exp_zero]
    calc
      _ = Real.exp (-(L * t)) * (Real.exp (l * t) * B t l l0) := by rw [← mul_assoc, he1]
      _ ≤ Real.exp (-(L * t)) * (Real.exp (L * t) * B t L l0) := hh
      _ = _ := by rw [← mul_assoc, he2, one_mul]
  · have h' : L ≤ l := (lt_of_not_ge h).le
    rw [max_eq_right (sub_nonpos.mpr h')]
    simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
    exact (B_nonneg_order t L l l0 ht hLp h0 h').2

#print axioms lemma2_3

end LeanLab.Zhao2025.Task56
