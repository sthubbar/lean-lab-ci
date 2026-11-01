import LeanLab.ChenExplicit.Yamada

open Finset Real
open scoped Classical

namespace LeanLab.ChenExplicit.Yamada

/-- REDUCTION for `thm51_leaf1`. The missing analytic result is Yamada 2015, Theorem 5.1,
equation (56): with `z = N^{1/8}`, `S(A, P(z)) > U_N |A| / log N * (4 e^gamma log 3 -
0.5198 eps0(N) - 767.7471 / log^2 N)`. The lab's leaf uses the weaker error term
`767.7471 / sqrt(log N)`, which is larger than `767.7471 / log^2 N` for `log N > 1`, so the
paper's (56) implies the leaf. This lemma checks that implication elementarily. The sieve
estimate (56) itself, whose proof in the paper runs through Lemma 5.2 (Buchstab inclusion
exclusion), Lemma 5.3 (sieve bounds from Theorem 3.1) and the alternating sum evaluations
(70), (79), (83), is absent from Mathlib: Mathlib has only the Selberg upper bound sieve
(`Mathlib.NumberTheory.SelbergSieve`), with no lower bound sieve and no explicit constants. -/
theorem thm51_leaf1_of_eq56 (N : ℕ) (hL1 : 1 ≤ log (N : ℝ))
    (h56 : U N * Acard N / log (N : ℝ) *
        (4 * exp eulerMascheroniConstant * log 3 - 5198 / 10000 * eps0 N -
          7677471 / 10000 / log (N : ℝ) ^ 2) < (SA N (zN N) : ℝ)) :
    U N * Acard N / log (N : ℝ) * (4 * exp eulerMascheroniConstant * log 3) <
      (SA N (zN N) : ℝ) +
        U N * Acard N / log (N : ℝ) *
          (5198 / 10000 * eps0 N + 7677471 / 10000 / √(log (N : ℝ))) := by
  set M : ℝ := U N * Acard N / log (N : ℝ) with hM
  set L : ℝ := log (N : ℝ) with hL
  have hL0 : 0 < L := by linarith
  have hM0 : 0 ≤ M := by
    have hU := U_ge N
    rw [hM]
    exact div_nonneg (mul_nonneg (by linarith) (by positivity)) hL0.le
  have hsqr : √L ≤ L ^ 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [one_le_pow₀ hL1 (n := 3)]
  have hdiv : 7677471 / 10000 / L ^ 2 ≤ 7677471 / 10000 / √L := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hsqr (by norm_num)
  have hmono : M * (4 * exp eulerMascheroniConstant * log 3 -
      5198 / 10000 * eps0 N - 7677471 / 10000 / √L)
      ≤ M * (4 * exp eulerMascheroniConstant * log 3 -
        5198 / 10000 * eps0 N - 7677471 / 10000 / L ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hM0
  have e1 : M * (4 * exp eulerMascheroniConstant * log 3 -
      5198 / 10000 * eps0 N - 7677471 / 10000 / √L)
      = M * (4 * exp eulerMascheroniConstant * log 3) -
        M * (5198 / 10000 * eps0 N) - M * (7677471 / 10000 / √L) := by ring
  have e2 : M * (4 * exp eulerMascheroniConstant * log 3 -
      5198 / 10000 * eps0 N - 7677471 / 10000 / L ^ 2)
      = M * (4 * exp eulerMascheroniConstant * log 3) -
        M * (5198 / 10000 * eps0 N) - M * (7677471 / 10000 / L ^ 2) := by ring
  have e3 : M * (5198 / 10000 * eps0 N + 7677471 / 10000 / √L)
      = M * (5198 / 10000 * eps0 N) + M * (7677471 / 10000 / √L) := by ring
  rw [e3]
  rw [e1] at hmono
  rw [e2] at h56
  linarith

/-- LEAF. Yamada 2015, Theorem 5.1 part 1 -/
theorem thm51_leaf1 (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) :
    U N * Acard N / log (N : ℝ) * (4 * exp eulerMascheroniConstant * log 3) < (SA N (zN N) : ℝ) +
    U N * Acard N / log (N : ℝ) * (5198 / 10000 * eps0 N + 7677471 / 10000 / √(log (N : ℝ))) := by
  sorry

/-- LEAF. Yamada 2015, Theorem 5.1 part 2 -/
theorem thm51_leaf2 (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) : True := by trivial

/-- LEAF. Yamada 2015, Theorem 5.1 part 3 -/
theorem thm51_leaf3 (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) : True := by trivial

/-- LEAF. Yamada 2015, Theorem 5.1 part 4 -/
theorem thm51_leaf4 (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) : True := by trivial

/-- LEAF. Yamada 2015, Theorem 5.1 part 5 -/
theorem thm51_leaf5 (N : ℕ) (hEven : Even N) (hN : exp (exp 36) < (N : ℝ)) : True := by trivial


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
