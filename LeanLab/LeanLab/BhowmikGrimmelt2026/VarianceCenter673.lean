/-
An audit of the centering in the sealed V definition.
P0029 page 22 subtracts H after the finite sum.
The Lean notation also puts that subtraction after the sum.
These diagnostics change no sealed statement or definition.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

/-- The current V definition has exactly the centering printed on page 22. -/
theorem variance_centering_identity673 (X H : ℝ) :
    V X H = ∫ x in X..(2 * X),
      ((∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, vonMangoldt n) - H) ^ 2 := by
  rfl

/-- At x equal to H equal to two the two centering conventions differ. -/
theorem variance_centering_counterexample673 :
    (∑ n ∈ Finset.Ioc 2 4, (vonMangoldt n - (2 : ℝ))) ≠
      (∑ n ∈ Finset.Ioc 2 4, vonMangoldt n) - 2 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  norm_num only [Nat.card_Ioc, Nat.reduceSub, Nat.cast_ofNat]
  intro h
  linarith

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.variance_centering_identity673
#print axioms LeanLab.BhowmikGrimmelt2026.variance_centering_counterexample673
