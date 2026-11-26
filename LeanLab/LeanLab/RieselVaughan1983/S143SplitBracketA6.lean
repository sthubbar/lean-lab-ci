import LeanLab.RieselVaughan1983.Lemma4From393

/-! Split of the leaf `S106SplitDecomp93.bracket_A6_lower`.
Riesel and Vaughan 1983, Ark. Mat. 21, page 46 display 2.14 and page 47 display 2.20.
The lower bracket of A6 at lambda = 3/2 follows from the printed lower bound of A3
in display 2.14 together with the Mathlib bounds on log 2 and log 3.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.S143SplitBracketA6
open Real
open LeanLab.RieselVaughan1983.Lemma2 LeanLab.RieselVaughan1983.Lemma4From393
noncomputable section

/-- LEAF: Riesel and Vaughan 1983 page 46 display 2.14, lower bound of A3. HARD, cited numerical evaluation of the prime sum A0 and of Euler's constant. -/
theorem a3_lower_214 : (6023476 / 1000000 : ℝ) < A3 := by
  sorry

/-- The page 47 display 2.20 lower bracket of A6 at lambda = 3/2, from display 2.14.
CONDITIONAL ON the hypothesis `h`, the display 2.14 lower bound of A3. -/
theorem bracket_A6_lower_of_h214 (h : (6023476 / 1000000 : ℝ) < A3) :
    (8463433 / 1000000 : ℝ) ≤ A6 (3 / 2) := by
  have h2 : log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h3 : log 3 < 1.0986122888 := Real.log_three_lt_d9
  have hsplit : log (3 / 2 : ℝ) = log 3 - log 2 := by
    rw [log_div (by norm_num) (by norm_num)]
  unfold A6
  rw [hsplit]
  norm_num at h2 h3 ⊢
  linarith

/-- The page 47 display 2.20 lower bracket of A6 at lambda = 3/2.
CONDITIONAL ON the leaf `a3_lower_214`. Exactly the statement of
`S106SplitDecomp93.bracket_A6_lower`. -/
theorem bracket_A6_lower_of_214 : (8463433 / 1000000 : ℝ) ≤ A6 (3 / 2) :=
  bracket_A6_lower_of_h214 a3_lower_214

end
end LeanLab.RieselVaughan1983.S143SplitBracketA6

#print axioms LeanLab.RieselVaughan1983.S143SplitBracketA6.bracket_A6_lower_of_h214
#print axioms LeanLab.RieselVaughan1983.S143SplitBracketA6.bracket_A6_lower_of_214
