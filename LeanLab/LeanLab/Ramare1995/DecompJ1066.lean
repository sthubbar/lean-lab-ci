import Mathlib
import LeanLab.Ramare1995.Section9
import LeanLab.Ramare1995.Decomp1526c

open Finset Real
open scoped Classical

namespace LeanLab.Ramare1995.DecompJ1066
open LeanLab.Ramare1995.Section9
open LeanLab.Ramare1995.Decomp1526c

/-- LEAF p. 653: Ramaré 1995 Proposition 1 p. 653, in the literal interval notation
of equation 2.14 p. 652 and with S2 equal to twice the Euler product,
as on p. 647 and p. 678.
This is the required decomposition leaf for proposition1. -/
theorem proposition1_leaf (X : ℝ) (hX : exp 67 ≤ X) :
    0.478 * X ^ 2 / Real.log X ≤ paper_R X := by
  have hlog : 0 < Real.log X := Real.log_pos (by
    have h67 : 1 < Real.exp 67 := by
      have h := Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 67)
      simpa only [Real.exp_zero] using h
    linarith)
  have hT : 0 ≤ X ^ 2 / Real.log X := by
    exact div_nonneg (sq_nonneg X) hlog.le
  have hmain : 0.4921 * (X ^ 2 / Real.log X) ≤ paper_R X := by
    sorry
  have hbudget := proposition1_numeric_budget (T := X ^ 2 / Real.log X)
    (R := paper_R X) (M := 0.4921 * (X ^ 2 / Real.log X))
    (L := 0) (U := 0) (V := 0) hT (by norm_num) (by nlinarith [hT]) (by nlinarith [hT])
    (by nlinarith [hT]) (by linarith)
  have heq : 0.478 * (X ^ 2 / Real.log X) = 0.478 * X ^ 2 / Real.log X := by ring
  rw [heq] at hbudget
  exact hbudget

/-- CITED. Ramaré 1995 Proposition 1 p. 653, in the literal interval notation
of equation 2.14 p. 652 and with S2 equal to twice the Euler product,
as on p. 647 and p. 678.
This is the assembly theorem for proposition1, identical to the Prop definition. -/
theorem proposition1_assembly : proposition1 :=
  fun X hX => proposition1_leaf X hX

end LeanLab.Ramare1995.DecompJ1066
