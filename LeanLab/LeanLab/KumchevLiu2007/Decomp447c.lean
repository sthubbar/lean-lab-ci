/-
Euler product decomposition of the weighted smooth fractional moment.
Source https://arxiv.org/abs/0801.0130 page 14 below display 50.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.EulerProduct447
import LeanLab.KumchevLiu2007.SmoothEuler447

namespace LeanLab.KumchevLiu2007.Task447c
open Real Task129b Task438d
open scoped BigOperators

/-- LEAF. Page 14 below display 50, derived finite prime Euler product step.
Each local positive prime power has coefficient 64. Its reciprocal power
series contributes 64 divided by p to s minus 1. Only this finite support
comparison is required. No logarithmic bound is asserted. -/
theorem smooth_moment_euler_bound (Q : ℝ) (M : ℕ) (hQ : 0 < Q) (s : ℝ) (hs : 0 < s) :
    (∑ q ∈ Finset.Icc 1 M,
      smoothWeight q Q * coefficientMajorant q / (q : ℝ) ^ s) ≤
      ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime,
        (1 + 64 / ((p : ℝ) ^ s - 1)) := by
  exact SmoothEuler447.smooth_moment_euler_bound Q M hQ s hs

/-- LEAF. Page 14 below display 50, derived numerical prime product input.
The exponent moves by one over twice the maximum of 1 and log Q.
This isolates the uniform estimate for an explicit finite prime product.
There is no smooth indicator, modulus sum, tail, x or y variable. -/
theorem fractional_euler_product_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ Q : ℝ, 0 < Q →
      (∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime,
        (1 + 64 / ((p : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q))) - 1))) ≤
        C * (max 1 (Real.log Q)) ^ D := by
  exact EulerProduct447.fractional_euler_product_bound

/-- Page 14 below display 50. Exact Task447b.smooth_fractional_moment
from its finite Euler product comparison and uniform prime product bound.
Both smaller inputs have clean proofs. -/
theorem smooth_fractional_moment :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ (Q : ℝ) (M : ℕ), 0 < Q →
      (∑ q ∈ Finset.Icc 1 M,
        smoothWeight q Q * coefficientMajorant q /
          (q : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q)))) ≤
        C * (max 1 (Real.log Q)) ^ D := by
  obtain ⟨C, D, hC, hD, hb⟩ := fractional_euler_product_bound
  refine ⟨C, D, hC, hD, ?_⟩
  intro Q M hQ
  have hV : (1 : ℝ) ≤ max 1 (Real.log Q) := le_max_left _ _
  have hs : 0 < 1 - 1 / (2 * max 1 (Real.log Q)) := by
    have hh : 1 / (2 * max 1 (Real.log Q)) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  exact (smooth_moment_euler_bound Q M hQ _ hs).trans (hb Q hQ)

#print axioms smooth_moment_euler_bound
#print axioms fractional_euler_product_bound
#print axioms smooth_fractional_moment
end LeanLab.KumchevLiu2007.Task447c
