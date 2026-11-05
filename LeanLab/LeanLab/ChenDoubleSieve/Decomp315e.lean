import LeanLab.ChenDoubleSieve.Decomp315d
import LeanLab.ChenDoubleSieve.Decomp275e
import LeanLab.ChenDoubleSieve.Decomp275f
import LeanLab.ChenDoubleSieve.Decomp275g

/-!
Supply split for Wu 2004 Section 10.
Source: https://arxiv.org/pdf/0705.1652, pages 38 to 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- LEAF. Wu 2004 page 42 final numerical display, F13.
The actual fourfold Buchstab integral satisfies its printed upper bound. -/
theorem numerical_F13 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 10 ≤ 0.023310 := by
  sorry

/-- LEAF. Wu 2004 page 42 final numerical display, F14.
The actual fourfold Buchstab integral satisfies its printed upper bound. -/
theorem numerical_F14 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 11 ≤ 0.182860 := by
  sorry

/-- The exact integral_evaluation statement follows from eight smaller leaves
and the four existing certified logarithmic coefficients. OPEN through those eight leaves. -/
theorem integral_evaluation_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    (3344307 : ℝ) / 4000000 ≤ weighted (integralTerms F f ω) / 4 := by
  have h0 := numerical_F0 F f ω h hω
  have h1 := numerical_F1 F f ω h hω
  have h2 := numerical_F2 F f ω h hω
  have h3 := numerical_F3 F f ω h hω
  have h4 := numerical_F4 F f ω h hω
  have h5 := numerical_F5 F f ω h hω
  have h13 := numerical_F13 F f ω h hω
  have h14 := numerical_F14 F f ω h hω
  have h7 := Thm2Scalar.F7_upper F f ω
  have h8 := Thm2Scalar.F8_upper F f ω
  have h9 := Thm2Scalar.F9_upper F f ω
  have h10 := Thm2Scalar.F10_upper F f ω
  dsimp only [weighted]
  linarith only [h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h13, h14]

end LeanLab.ChenDoubleSieve.Task315
