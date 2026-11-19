import Mathlib

/-!
Numerical conversion used for the cited Mertens bound on Liu and Wang page 172.
Source Rosser and Schoenfeld 1962, page 70, Theorem 6, displays 3.21 and 3.22,
with the printed constant E in display 2.11 on page 65.
The analytic estimate is an explicit hypothesis. It is not proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task655

/-- Derived logarithm threshold for the numerical conversion on page 172. -/
theorem log15000_lower : (9.6 : ℝ) ≤ Real.log 15000 := by
  have hpow : Real.exp 1 ^ 10 ≤ (2.7182818286 : ℝ) ^ 10 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 10
  have hten : Real.exp (10 : ℝ) = Real.exp 1 ^ 10 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 10
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.4) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have hsmall : Real.exp (10 : ℝ) < 15000 * Real.exp 0.4 := by
    rw [hten]
    norm_num only at hpow
    nlinarith
  have he : Real.exp (9.6 : ℝ) < 15000 := by
    have hident : Real.exp (9.6 : ℝ) * Real.exp 0.4 = Real.exp 10 := by
      rw [← Real.exp_add]
      norm_num
    by_contra hn
    have hn' : (15000 : ℝ) ≤ Real.exp 9.6 := le_of_not_gt hn
    have hmul := mul_le_mul_of_nonneg_right hn' (Real.exp_pos (0.4 : ℝ)).le
    rw [hident] at hmul
    linarith
  exact (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 15000)).mpr he.le

/-- Arithmetic conversion of the cited Theorem 6 error to the constants on
Liu and Wang page 172. CONDITIONAL ON hError when S is the prime logarithm sum. -/
theorem mertens_constants_of_error (x E S : ℝ) (hx : 15000 ≤ x)
    (hElo : -1.33259 ≤ E) (hEhi : E ≤ -1.33258)
    (hError : |S - (Real.log x + E)| ≤ 1 / (2 * Real.log x)) :
    Real.log x - 1.385 ≤ S ∧ S ≤ Real.log x - 1.28 := by
  have hlog : (9.6 : ℝ) ≤ Real.log x := log15000_lower.trans
    (Real.log_le_log (by norm_num : (0 : ℝ) < 15000) hx)
  have hden : (0 : ℝ) < 2 * Real.log x := by linarith
  have hinv : 1 / (2 * Real.log x) ≤ (0.0521 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hError
  constructor <;> linarith

/-- The three numerical premises in the scalar conversion have a concrete
instance. This does not assert an analytic estimate for the prime sum. -/
theorem mertens_constants_instance :
    (-1.33259 : ℝ) ≤ -1.332585 ∧ (-1.332585 : ℝ) ≤ -1.33258 ∧
      |(Real.log 15000 - 1.332585) - (Real.log 15000 + (-1.332585))| ≤
        1 / (2 * Real.log 15000) := by
  have hlog : (0 : ℝ) < Real.log 15000 := lt_of_lt_of_le (by norm_num) log15000_lower
  constructor
  · norm_num
  constructor
  · norm_num
  have he : (Real.log (15000 : ℝ) - 1.332585) - (Real.log 15000 + (-1.332585)) = 0 := by ring
  rw [he, abs_zero]
  positivity

end LeanLab.LiuWang2002.Task655

#print axioms LeanLab.LiuWang2002.Task655.log15000_lower
#print axioms LeanLab.LiuWang2002.Task655.mertens_constants_of_error
#print axioms LeanLab.LiuWang2002.Task655.mertens_constants_instance
