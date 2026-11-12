/-
Exact supply of the local Lemma 3.8 leaf of Task129, Kumchev and Liu,
arXiv 0801.0130, page 14 display 49 for j = 2. The proof chain of
Task342e.lemma38_two_proved imports Decomp129, so Decomp129 cannot use it
directly; this file closes the local twin downstream.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp342e

namespace LeanLab.KumchevLiu2007.Supply129r

open Real Complex LeanLab.KumchevLiu2007 Task129 Task129b

/-- Page 13 display 45: the local product of Decomp129 is the product of Decomp129b. -/
theorem partialProduct2_eq_product2 (n : ℕ) (Q : ℝ) :
    partialProduct2 n Q = product2 n Q := rfl

/-- Page 14 display 49, Lemma 3.8 for j = 2. The exact statement of
Task129.lemma38_two_local, supplied from Task342e.lemma38_two_proved. -/
theorem lemma38_two_local_supply (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧
    ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ‖series2 n P - partialProduct2 n Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) :=
  Task342e.lemma38_two_proved A ε hA hε

end LeanLab.KumchevLiu2007.Supply129r
