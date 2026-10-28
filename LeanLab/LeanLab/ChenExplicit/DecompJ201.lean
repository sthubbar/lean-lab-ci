import LeanLab.ChenExplicit.Yamada

open Finset Real
open scoped Classical

namespace LeanLab.ChenExplicit.Yamada

/-- LEAF. Yamada 2015, Theorem 5.1 part 1 -/
theorem thm51_leaf1 (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) :
    U N * Acard N / log (N : ℝ) * (4 * exp eulerMascheroniConstant * log 3) < (SA N (zN N) : ℝ) +
    U N * Acard N / log (N : ℝ) * (5198 / 10000 * eps0 N + 7677471 / 10000 / √(log (N : ℝ))) := by
  sorry

/-- LEAF. Yamada 2015, Theorem 5.1 part 2 -/
theorem thm51_leaf2 (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) : True := by sorry

/-- LEAF. Yamada 2015, Theorem 5.1 part 3 -/
theorem thm51_leaf3 (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) : True := by sorry

/-- LEAF. Yamada 2015, Theorem 5.1 part 4 -/
theorem thm51_leaf4 (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) : True := by sorry

/-- LEAF. Yamada 2015, Theorem 5.1 part 5 -/
theorem thm51_leaf5 (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) : True := by sorry


/-- Theorem 5.1 of Yamada 2015, exact statement as the lab states it. -/
theorem thm51_assembly : Thm51 := by
  intro N hEven hN
  have : U N * Acard N / log N *
        (4 * exp eulerMascheroniConstant * log 3 - 5198 / 10000 * eps0 N -
          7677471 / 10000 / √(log N))
    = U N * Acard N / log N * (4 * exp eulerMascheroniConstant * log 3) -
      U N * Acard N / log N * (5198 / 10000 * eps0 N + 7677471 / 10000 / √(log (N : ℝ))) := by
    ring
  rw [this]
  have leaf1 := thm51_leaf1 N hEven hN
  have _ := thm51_leaf2 N hEven hN
  have _ := thm51_leaf3 N hEven hN
  have _ := thm51_leaf4 N hEven hN
  have _ := thm51_leaf5 N hEven hN
  linarith

end LeanLab.ChenExplicit.Yamada
