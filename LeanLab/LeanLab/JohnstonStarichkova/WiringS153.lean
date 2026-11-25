/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3, page 3 and page 13.
Wiring audit, burst-20261122 session S153. The LEAFs exp_neg_euler_gt and twin_prime_const_gt of
SPLIT_sifted_count_lower_v3.lean have exact twins exp_neg_euler_gt_split and
twin_prime_const_gt_split, now PROVED with no sorry, in files that import that file, so the LEAFs
cannot be closed in place. This file states sifted_count_lower_v3_wired, the exact statement of
sifted_count_lower_v3_split, with the same proof but through the proved twins: it is
CONDITIONAL ON sifted_count_lower_UN alone.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.JohnstonStarichkova.SPLIT_exp_neg_euler_gt
import LeanLab.JohnstonStarichkova.SPLIT_twin_prime_const_gt

namespace LeanLab.JohnstonStarichkova
open LeanLab.AlmostPrimes

example : type_of% exp_neg_euler_gt_split = type_of% exp_neg_euler_gt := rfl
example : type_of% twin_prime_const_gt_split = type_of% twin_prime_const_gt := rfl

/-- P0019 v3 page 13, proof of Theorem 1.3: S(A, P(z)) > 3.7 N / log^2 N for even N at least
exp(exp 7.9). CONDITIONAL ON sifted_count_lower_UN; the two constant bounds are PROVED. -/
theorem sifted_count_lower_v3_wired (N : ℕ) (hN : Even N) (hX : Real.exp (Real.exp 7.9) ≤ N) :
    3.7 * (N : ℝ) / Real.log N ^ 2 <
      (({p : ℕ | p.Prime ∧ p < N ∧ ¬ p ∣ N ∧
        ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40} : Set ℕ).ncard : ℝ) := by
  refine lt_trans ?_ (sifted_count_lower_UN N hN hX)
  have he := exp_neg_euler_gt_split
  have hc := twin_prime_const_gt_split
  set E := Real.exp (-Real.eulerMascheroniConstant)
  set C := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hX
  have hN1 : (1 : ℝ) < N := by
    refine lt_of_lt_of_le ?_ hX
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (Real.exp_pos _)
  have hL : 0 < Real.log N := Real.log_pos hN1
  have hEC : (0.56145 : ℝ) * 0.66016 < E * C := by
    have : (0.56145 : ℝ) * 0.66016 < E * 0.66016 := by nlinarith
    have h2 : E * 0.66016 < E * C := by
      have : 0 < E := Real.exp_pos _
      nlinarith
    linarith
  have hk : (3.7 : ℝ) < 5 * (2 * E * C) := by nlinarith
  have hpos : 0 < (N : ℝ) / Real.log N ^ 2 := by positivity
  have := mul_lt_mul_of_pos_right hk hpos
  calc 3.7 * (N : ℝ) / Real.log N ^ 2 = 3.7 * ((N : ℝ) / Real.log N ^ 2) := by ring
    _ < 5 * (2 * E * C) * ((N : ℝ) / Real.log N ^ 2) := this
    _ = 5 * (2 * E * C) * (N : ℝ) / Real.log N ^ 2 := by ring


example : type_of% @sifted_count_lower_v3_wired = type_of% @sifted_count_lower_v3_split := rfl

end LeanLab.JohnstonStarichkova
