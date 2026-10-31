/-
P0001, arXiv 1312.7748v2, Section 7.2, page 60, the unnumbered display right
after 7.19: |phi log+|_inf <= 0.381157 by bisection, phi(t) = t^2 e^(-t^2/2).
Unit U-8000 T1. Page checked against the arXiv PDF in review, 2026-10-22.
AI wrote this Lean code. Binary Goldbach remains open.
-/
import Mathlib

open Real Finset

namespace LeanLab.Helfgott2013.SectionSevenSup

/-- Certified rational bounds at the tangent point x = 1.7856. -/
theorem tangent_constants :
    Real.log (3.5712 : ℝ) ≤ 1.272901674 ∧
    (5.963156768 : ℝ) ≤ Real.exp 1.7856 := by
  constructor
  · apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3.5712)).2
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.272901674) 18
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.7856) 23
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith

#print axioms tangent_constants

/-- A squared exponential tangent, valid throughout the required half-line. -/
theorem exp_lower {x : ℝ} (hx : 1 / 2 ≤ x) :
    (5.963156768 : ℝ) * (1 + (x - 1.7856) / 2) ^ 2 ≤ Real.exp x := by
  have ht : 0 ≤ 1 + (x - 1.7856) / 2 := by linarith
  have he := Real.add_one_le_exp ((x - 1.7856) / 2)
  have hp := Real.exp_pos ((x - 1.7856) / 2)
  have hs : (1 + (x - 1.7856) / 2) ^ 2 ≤
      Real.exp ((x - 1.7856) / 2) ^ 2 := by nlinarith
  calc
    (5.963156768 : ℝ) * (1 + (x - 1.7856) / 2) ^ 2 ≤
        Real.exp 1.7856 * Real.exp ((x - 1.7856) / 2) ^ 2 :=
      mul_le_mul tangent_constants.2 hs (sq_nonneg _) (Real.exp_pos _).le
    _ = Real.exp x := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

#print axioms exp_lower

/-- The rational comparison after applying the logarithmic tangent. -/
theorem quadratic_comparison (x : ℝ) :
    x * (1.272901674 + (x - 1.7856) / 1.7856) ≤
      (0.381157 : ℝ) * (5.963156768 * (1 + (x - 1.7856) / 2) ^ 2) := by
  let A : ℝ := 0.381157 * 5.963156768 / 4 - 1 / 1.7856
  let B : ℝ := 0.381157 * 5.963156768 - 1.272901674 - 1
  have hs := sq_nonneg (x - 1.7856 + B / (2 * A))
  dsimp [A, B] at hs
  norm_num at hs ⊢
  nlinarith only [hs]

#print axioms quadratic_comparison

/-- The exact numerical supremum bound behind Helfgott's display 7.19. -/
theorem phi_log_sup {t : ℝ} (ht : 1 ≤ t) :
    t ^ 2 * Real.exp (-t ^ 2 / 2) * Real.log t ≤ (0.381157 : ℝ) := by
  let x : ℝ := t ^ 2 / 2
  have ht0 : 0 < t := by linarith
  have hx : 1 / 2 ≤ x := by dsimp [x]; nlinarith
  have hl := Real.log_le_sub_one_of_pos
    (show 0 < t ^ 2 / (3.5712 : ℝ) by positivity)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hl
  norm_num at hl
  have hlog : 2 * Real.log t ≤ 1.272901674 + (x - 1.7856) / 1.7856 := by
    have hc := tangent_constants.1
    dsimp [x]
    norm_num at hl hc ⊢
    nlinarith only [hl, hc]
  have hm := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ x)
  have hq := quadratic_comparison x
  have he := mul_le_mul_of_nonneg_left (exp_lower hx)
    (by norm_num : (0 : ℝ) ≤ 0.381157)
  have hnum : t ^ 2 * Real.log t ≤ 0.381157 * Real.exp x := by
    dsimp [x] at hm hq he ⊢
    nlinarith only [hm, hq, he]
  have hcancel : Real.exp x * Real.exp (-t ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]
    have hz : x + -t ^ 2 / 2 = 0 := by dsimp [x]; ring
    rw [hz, Real.exp_zero]
  calc
    t ^ 2 * Real.exp (-t ^ 2 / 2) * Real.log t =
        (t ^ 2 * Real.log t) * Real.exp (-t ^ 2 / 2) := by ring
    _ ≤ (0.381157 * Real.exp x) * Real.exp (-t ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hnum (Real.exp_pos _).le
    _ = 0.381157 := by rw [mul_assoc, hcancel, mul_one]

#print axioms phi_log_sup

end LeanLab.Helfgott2013.SectionSevenSup
