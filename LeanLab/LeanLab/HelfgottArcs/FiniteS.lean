/-
Finite support of the minor arc exponential sum.
Source: https://arxiv.org/abs/1205.5252v4, page 3, equations 1.1 and 1.4.
These are elementary consequences of the paper's compact smoothing weight.
AI wrote this Lean code for CODEX task81. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.FourierWeights

namespace LeanLab.HelfgottArcs
open scoped ArithmeticFunction
open Finset

/-- The infinite notation for S eta2 is a finite sum below the ceiling of x. -/
theorem S_eta2_eq_sum (α x : ℝ) (hx : 0 < x) :
    S eta2 α x = ∑ n ∈ range (Nat.ceil x),
      ((Λ n : ℝ) : ℂ) * e (α * n) * (eta2 (n / x) : ℂ) := by
  unfold S
  apply tsum_eq_sum
  intro n hn
  have hn' : Nat.ceil x ≤ n := Nat.le_of_not_gt (by simpa only [mem_range] using hn)
  have hxn : x ≤ n := (Nat.le_ceil x).trans (by exact_mod_cast hn')
  have hdiv : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hx).mpr (by simpa using hxn)
  have hz : eta2 ((n : ℝ) / x) = 0 := by
    apply le_antisymm _ (eta2_nonneg _)
    apply le_of_not_gt
    intro hp
    have hs := (eta2_pos_iff _).mp hp
    linarith [hs.2]
  simp only [hz, Complex.ofReal_zero, mul_zero]

/-- The unconditional triangle bound retains the weight but loses phase cancellation. -/
theorem norm_S_eta2_le_sum (α x : ℝ) (hx : 0 < x) :
    ‖S eta2 α x‖ ≤ ∑ n ∈ range (Nat.ceil x), (Λ n : ℝ) * eta2 (n / x) := by
  rw [S_eta2_eq_sum α x hx]
  refine (norm_sum_le _ _).trans_eq ?_
  apply sum_congr rfl
  intro n hn
  rw [norm_mul, norm_mul, norm_e, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_of_nonneg (eta2_nonneg _)]
  ring

/-- A coarse explicit estimate that does not use any minor arc cancellation. -/
theorem norm_S_eta2_le_coarse (α x : ℝ) (hx : 1 ≤ x) :
    ‖S eta2 α x‖ ≤ (Nat.ceil x : ℝ) * (4 * Real.log 2 * Real.log x) := by
  have hx0 : 0 < x := by linarith
  refine (norm_S_eta2_le_sum α x hx0).trans ?_
  calc ∑ n ∈ range (Nat.ceil x), (Λ n : ℝ) * eta2 (n / x)
      ≤ ∑ _n ∈ range (Nat.ceil x), 4 * Real.log 2 * Real.log x := by
        apply sum_le_sum
        intro n hn
        by_cases hn0 : n = 0
        · subst n
          simp only [ArithmeticFunction.map_zero, zero_mul]
          exact mul_nonneg (mul_nonneg (by norm_num)
            (Real.log_nonneg (by norm_num))) (Real.log_nonneg hx)
        · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
          have hnx : (n : ℝ) < x := Nat.lt_ceil.mp (mem_range.mp hn)
          have hl : (Λ n : ℝ) ≤ Real.log x := ArithmeticFunction.vonMangoldt_le_log.trans
            (Real.log_le_log hnpos hnx.le)
          have he := eta2_le ((n : ℝ) / x)
          have hmul := mul_le_mul hl he (eta2_nonneg _) (Real.log_nonneg hx)
          nlinarith
    _ = (Nat.ceil x : ℝ) * (4 * Real.log 2 * Real.log x) := by simp

end LeanLab.HelfgottArcs
