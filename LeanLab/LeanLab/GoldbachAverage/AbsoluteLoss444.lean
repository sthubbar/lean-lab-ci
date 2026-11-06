import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
A negative result for the absolute zero summation route to BHMS page 17.
Source context: https://arxiv.org/abs/1704.06103v2 pages 17 and 18.
This is a derived asymptotic obstruction, not a paper assertion.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.AbsoluteLoss444
open Filter Asymptotics

/-- The absolute summation route cannot absorb a positive power loss into log squared.
This is the size obstruction for the truncated explicit formula error on BHMS page 17. -/
theorem power_not_log_square (δ : ℝ) (hδ : 0 < δ) :
    ¬ (fun x : ℝ => x ^ δ) =O[atTop] (fun x : ℝ => Real.log x ^ 2) := by
  have hsmall : (fun x : ℝ => Real.log x ^ 2) =o[atTop] (fun x : ℝ => x ^ δ) := by
    simpa only [Real.rpow_two] using isLittleO_log_rpow_rpow_atTop 2 hδ
  apply hsmall.not_isBigO
  exact ((eventually_gt_atTop (1 : ℝ)).mono (fun x hx =>
    pow_ne_zero 2 (Real.log_pos hx).ne')).frequently

end LeanLab.GoldbachAverage.AbsoluteLoss444
