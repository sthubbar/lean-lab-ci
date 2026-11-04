import LeanLab.ChenDoubleSieve.Statements

/-!
Arithmetic from Wu 2004 page 42, final display of Section 10.
The existing thm2_eval statement contains no sieve function or integral.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ChenDoubleSieve.Task275

/-- The exact statement of thm2_eval is a rational identity inequality. -/
theorem thm2_eval_checked : (83607 : ℝ) / 100000 ≤ 0.83607 := by
  norm_num

/-- The printed arithmetic combination on page 42 has exact value 0.83607675. -/
theorem printed_combination :
    (4 * (13.473613 : ℝ) - 3.891854 - 20.432098 - 17.327241 +
      0.697375 + 2.118119 - 2 * 0.004609 - 2 * 0.434368 -
      5.161945 - 5.468377 - 0.023310 - 0.182860) / 4 = 3344307 / 4000000 := by
  norm_num

/-- The printed combination exceeds 0.83607 by 0.00000675. -/
theorem printed_margin : (83607 : ℝ) / 100000 < 3344307 / 4000000 := by
  norm_num

end LeanLab.ChenDoubleSieve.Task275
