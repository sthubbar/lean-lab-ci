/-
Exact supply of the circle_input leaf `eq49_lemma38` of `Decomp129`,
Kumchev and Liu, arXiv 0801.0130, paper P0088, page 14 display 49,
Lemma 3.8 for j equal to 2. Route burst session 8, p3, 2026-11-12.
The proof chain of `Task342e.lemma38_two_proved` imports `Decomp129`, so
`Decomp129` cannot use it directly; this file closes the leaf's exact
statement downstream, through the bridge of `Decomp129c`. No import cycle.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp129c
import LeanLab.KumchevLiu2007.Decomp342e

namespace LeanLab.KumchevLiu2007.Supply129c

open Real Complex LeanLab.KumchevLiu2007 Task129 Task129b

/-- Page 14 display 49, Lemma 3.8 for j equal to 2. The exact statement of
`Task129.eq49_lemma38`, supplied from `Task342e.lemma38_two_proved` through
`Task129c.eq49_lemma38_of_lemma38_two`. -/
theorem eq49_lemma38_supply (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x →
      0 < P → P ≤ Q → Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ‖series2 n P - eulerP2 n Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) :=
  Task129c.eq49_lemma38_of_lemma38_two Task342e.lemma38_two_proved A ε hA hε

/-- Statement check: the supplied theorem has exactly the type of the leaf
`Task129.eq49_lemma38`; the equation typechecks only if the two statements
agree, and holds by proof irrelevance. -/
theorem eq49_lemma38_supply_same_statement :
    @Task129.eq49_lemma38 = @eq49_lemma38_supply := rfl

end LeanLab.KumchevLiu2007.Supply129c

#print axioms LeanLab.KumchevLiu2007.Task342e.lemma38_two_proved
#print axioms LeanLab.KumchevLiu2007.Supply129c.eq49_lemma38_supply
