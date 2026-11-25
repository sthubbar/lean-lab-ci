import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_logint
import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_values_explicit
import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_logint_F9
import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_logint_F10

/-!
SPLIT of `Task275.integral_evaluation` into the twelve six decimal values printed in the
final display of Wu 2004 Section 10, https://arxiv.org/pdf/0705.1652, page 42.
The weighted combination of the printed values equals 3344307/4000000 exactly, so the
parent follows by linear arithmetic. Each leaf is the paper's printed value, read as a
one sided bound in the direction the weight needs; the paper does not state its rounding
direction, so each leaf may need the last digit checked by certified integration.
This file imports Decomp275b because the parent's statement uses `weighted` and
`integralTerms` that live there; the original is not edited.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Int
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- SPLIT into leaf_explicit0 of Feed1122_Decomp275b_values_explicit: Wu 2004 page 42 final display, numerical value of F0, from equation 10.2, index 0 of integralTerms. -/
theorem leaf_value0 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    (13.473613 : ℝ) ≤ integralTerms F f ω 0 := by
  exact Feed1122ValuesExplicit.value0_of_explicit F f ω h hω

/-- SPLIT into leaf_explicit1 of Feed1122_Decomp275b_values_explicit: Wu 2004 page 42 final display, numerical value of F1, from equation 10.3, index 1 of integralTerms. -/
theorem leaf_value1 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    integralTerms F f ω 1 ≤ (3.891854 : ℝ) := by
  exact Feed1122ValuesExplicit.value1_of_explicit F f ω h hω

/-- SPLIT into leaf_explicit2 of Feed1122_Decomp275b_values_explicit: Wu 2004 page 42 final display, numerical value of F2, from equation 10.4, index 2 of integralTerms. -/
theorem leaf_value2 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    integralTerms F f ω 2 ≤ (20.432098 : ℝ) := by
  exact Feed1122ValuesExplicit.value2_of_explicit F f ω h hω

/-- SPLIT into leaf_explicit3 of Feed1122_Decomp275b_values_explicit: Wu 2004 page 42 final display, numerical value of F3, from equation 10.4, index 3 of integralTerms. -/
theorem leaf_value3 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    integralTerms F f ω 3 ≤ (17.327241 : ℝ) := by
  exact Feed1122ValuesExplicit.value3_of_explicit F f ω h hω

/-- SPLIT into leaf_explicit4 of Feed1122_Decomp275b_values_explicit: Wu 2004 page 42 final display, numerical value of F4, from equation 10.5, index 4 of integralTerms. -/
theorem leaf_value4 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    (0.697375 : ℝ) ≤ integralTerms F f ω 4 := by
  exact Feed1122ValuesExplicit.value4_of_explicit F f ω h hω

/-- SPLIT into leaf_explicit5 of Feed1122_Decomp275b_values_explicit: Wu 2004 page 42 final display, numerical value of F5, from equation 10.5, index 5 of integralTerms. -/
theorem leaf_value5 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    (2.118119 : ℝ) ≤ integralTerms F f ω 5 := by
  exact Feed1122ValuesExplicit.value5_of_explicit F f ω h hω

/-- PROVED from Feed1122_Decomp275b_logint: Wu 2004 page 42 final display, numerical value of F7, from equation 10.10, index 6 of integralTerms. -/
theorem leaf_value6 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    integralTerms F f ω 6 ≤ (0.004609 : ℝ) := by
  have h := Feed1122LogInt.logint_F7
  have he : (1 / sigma1 - 1 : ℝ) = 84 / 41 := by norm_num [sigma1]
  simp only [integralTerms, Matrix.cons_val]
  rw [he]
  exact h

/-- PROVED from Feed1122_Decomp275b_logint: Wu 2004 page 42 final display, numerical value of F8, from equation 10.11, index 7 of integralTerms. -/
theorem leaf_value7 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    integralTerms F f ω 7 ≤ (0.434368 : ℝ) := by
  have h := Feed1122LogInt.logint_F8
  have he : (1 / sigma2 - 1 : ℝ) = 359 / 141 := by norm_num [sigma2]
  simp only [integralTerms, Matrix.cons_val]
  rw [he]
  exact h

/-- PROVED from Feed1122_Decomp275b_logint_F9: Wu 2004 page 42 final display, numerical value of F9, from equation 10.12, index 8 of integralTerms. -/
theorem leaf_value8 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    integralTerms F f ω 8 ≤ (5.161945 : ℝ) := by
  simp only [integralTerms, Matrix.cons_val]
  norm_num [kappa1, sigma1]
  exact LeanLab.ChenDoubleSieve.Feed1122LogIntF9.logint_F9_normed

/-- PROVED from Feed1122_Decomp275b_logint_F10: Wu 2004 page 42 final display, numerical value of F10, from equation 10.11, index 9 of integralTerms. -/
theorem leaf_value9 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    integralTerms F f ω 9 ≤ (5.468377 : ℝ) := by
  simp only [integralTerms, Matrix.cons_val, kappa2, sigma2]
  exact LeanLab.ChenDoubleSieve.Feed1122LogIntF10.logint_F10

/-- LEAF: Wu 2004 page 42 final display, numerical value of F13, from equation 10.12, using omega at most 0.561522 on u at least 3.5, index 10 of integralTerms. Class HARD. -/
theorem leaf_value10 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    integralTerms F f ω 10 ≤ (0.023310 : ℝ) := by
  sorry

/-- LEAF: Wu 2004 page 42 final display, numerical value of F14, from equation 10.12, using omega at most 0.561522 on u at least 3.5, index 11 of integralTerms. Class HARD. -/
theorem leaf_value11 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    integralTerms F f ω 11 ≤ (0.182860 : ℝ) := by
  sorry

/-- The parent `integral_evaluation`, exactly as stated in Decomp275b, from the twelve leaves. -/
theorem integral_evaluation_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    (3344307 : ℝ) / 4000000 ≤ weighted (integralTerms F f ω) / 4 := by
  have h0 := leaf_value0 F f ω h hω
  have h1 := leaf_value1 F f ω h hω
  have h2 := leaf_value2 F f ω h hω
  have h3 := leaf_value3 F f ω h hω
  have h4 := leaf_value4 F f ω h hω
  have h5 := leaf_value5 F f ω h hω
  have h6 := leaf_value6 F f ω h hω
  have h7 := leaf_value7 F f ω h hω
  have h8 := leaf_value8 F f ω h hω
  have h9 := leaf_value9 F f ω h hω
  have h10 := leaf_value10 F f ω h hω
  have h11 := leaf_value11 F f ω h hω
  dsimp only [weighted]
  linarith

end LeanLab.ChenDoubleSieve.Task275.Feed1122Int
