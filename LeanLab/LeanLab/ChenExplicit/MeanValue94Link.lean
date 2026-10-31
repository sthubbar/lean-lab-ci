/-
AI wrote this Lean code. CODEX task94.
Remove the now proved MeanValueStep input from the existing plus 4 bounds.
The three remaining analytic inputs stay CONDITIONAL.
Source: Bordignon arXiv 1907.08327 Section 2 eqs 4, 5 and 9 and Theorem 1.3.
The nu specializations follow P0009 eqs 81 and 91.
Binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.MeanValue94
import LeanLab.ChenExplicit.U1490NuX1
import LeanLab.ChenExplicit.U1498MX3

namespace LeanLab.ChenExplicit.MeanValue94Link

open LeanLab.ChenExplicit.U1483 LeanLab.ChenExplicit.U1486 LeanLab.ChenExplicit.U1490

/-- CONDITIONAL ON ClassNumberPlus4, BordignonEq9 and BordignonThm13.
The mean value input is discharged by MeanValue94.meanValueStep. -/
theorem siegel_even_q_dep_plus (hC : ClassNumberPlus4) (h9 : BordignonEq9)
    (h13 : BordignonThm13) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ)
    (hq : (4e5 : ℝ) < q) (hqU : Real.log (q : ℝ) ≤ 250) (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - gapP q := by
  exact U1490.siegel_even_q_dep_plus hC MeanValue94.meanValueStep h9 h13 q χ hχ hq hqU β hβ

/-- CONDITIONAL ON ClassNumberPlus4, BordignonEq9 and BordignonThm13.
The uniform K bound no longer assumes MeanValueStep. -/
theorem siegel_even_upto_K_plus (hC : ClassNumberPlus4) (h9 : BordignonEq9)
    (h13 : BordignonThm13) {K : ℝ} (hKU : Real.log K ≤ 250) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ) (hq : (4e5 : ℝ) < q) (hqK : (q : ℝ) ≤ K)
    (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - 4 / (Real.sqrt K * Real.log K) := by
  exact U1490.siegel_even_upto_K_plus hC MeanValue94.meanValueStep h9 h13 hKU q χ hχ hq hqK β hβ

/-- CONDITIONAL ON ClassNumberPlus4, BordignonEq9 and BordignonThm13.
The x1 specialization no longer assumes MeanValueStep. -/
theorem nuP_siegel (hC : ClassNumberPlus4) (h9 : BordignonEq9)
    (h13 : BordignonThm13) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ)
    (hq : (4e5 : ℝ) < q) (hqK : (q : ℝ) ≤ U1490NuX1.K1) (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - U1490NuX1.nuP := by
  exact U1490NuX1.nuP_siegel hC MeanValue94.meanValueStep h9 h13 q χ hχ hq hqK β hβ

/-- CONDITIONAL ON ClassNumberPlus4, BordignonEq9 and BordignonThm13.
The x2 of X3 specialization no longer assumes MeanValueStep. -/
theorem nuP3_siegel (hC : ClassNumberPlus4) (h9 : BordignonEq9)
    (h13 : BordignonThm13) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ)
    (hq : (4e5 : ℝ) < q) (hqK : (q : ℝ) ≤ U1498MX3.K) (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - U1498MX3.νP := by
  exact U1498MX3.nuP3_siegel hC MeanValue94.meanValueStep h9 h13 q χ hχ hq hqK β hβ

#print axioms siegel_even_q_dep_plus
#print axioms siegel_even_upto_K_plus
#print axioms nuP_siegel
#print axioms nuP3_siegel

end LeanLab.ChenExplicit.MeanValue94Link
