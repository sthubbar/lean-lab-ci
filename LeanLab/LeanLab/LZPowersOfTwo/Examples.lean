/-
Languasco-Zaccagnini 2009, P0079, arXiv 0811.3663 v2: the two worked examples after the
Theorem, "λ1 = √3 = μ1⁻¹, λ2 = −√2 = μ2⁻¹ and η = 1, we get s0 = 61" and
"λ1 = π = μ1⁻¹, λ2 = −√2 = μ2⁻¹ and η = 1, we get s0 = 119".
The printed formulas (3) and (2), as encoded in `s0`, give much less: at most 27 and at most
60. Python gives exactly 24 and 52. The paper's 61 and 119 are reproduced exactly by
`2 + ⌈C(1,1)/(−log ν)⌉`, the formula with the numerator `log(2 C(1,1)|λ1λ2|/η)` replaced
by `C(1,1)` itself. The Theorem is unaffected: a larger s0 is a weaker true claim.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.LZPowersOfTwo.Statements

open Real

namespace LeanLab.LZPowersOfTwo

theorem Cq_one_one : Cq 1 1 = log 2 + bigC := by
  have h : 0 ≤ log 2 + bigC * Sprime 1 := by
    rw [Sprime_one]; have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    norm_num [bigC]; linarith
  rw [Cq, Real.mul_self_sqrt h, Sprime_one, mul_one]

theorem Cq_one_one_lt : Cq 1 1 < 10.7151 := by
  rw [Cq_one_one]
  have := Real.log_two_lt_d9
  norm_num [bigC] at this ⊢
  linarith

theorem Cq_one_one_pos : 0 < Cq 1 1 := by
  rw [Cq_one_one]
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  norm_num [bigC]; linarith

theorem exp_four_gt : (54 : ℝ) < exp 4 := by
  have h := Real.exp_one_gt_d9
  have : exp 4 = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h0 : (0 : ℝ) ≤ 2.7182818283 := by norm_num
  calc (54 : ℝ) < 2.7182818283 ^ 4 := by norm_num
    _ ≤ exp 1 ^ 4 := by gcongr

theorem exp_five_gt : (148 : ℝ) < exp 5 := by
  have h := Real.exp_one_gt_d9
  have : exp 5 = exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h0 : (0 : ℝ) ≤ 2.7182818283 := by norm_num
  calc (148 : ℝ) < 2.7182818283 ^ 5 := by norm_num
    _ ≤ exp 1 ^ 5 := by gcongr

/-- `−log ν ≥ 1 − ν`. -/
theorem neg_log_ge {ν : ℝ} (hν : 0 < ν) : 1 - ν ≤ -log ν := by
  have := Real.log_le_sub_one_of_pos hν
  linarith

/-- The ceiling step: a numerator below `A` and a denominator at least `B > 0` give
`s0 ≤ 2 + ⌈A/B⌉`. -/
theorem s0_le_of {ν l1 l2 η A B : ℝ} {q1 q2 : ℕ} (hB : 0 < B) (hA : 0 ≤ A)
    (hnum : log (2 * Cq q1 q2 * |l1 * l2|) - log η ≤ A) (hden : B ≤ -log ν) :
    s0 ν l1 l2 q1 q2 η ≤ 2 + ⌈A / B⌉ := by
  unfold s0
  have hden' : 0 < -log ν := lt_of_lt_of_le hB hden
  have : (log (2 * Cq q1 q2 * |l1 * l2|) - log η) / (-log ν) ≤ A / B := by
    calc (log (2 * Cq q1 q2 * |l1 * l2|) - log η) / (-log ν) ≤ A / (-log ν) := by
          gcongr
      _ ≤ A / B := by gcongr
  have := Int.ceil_mono this
  linarith

/-- **Example 1 under formula (3)**: `λ1 = √3`, `λ2 = −√2`, `q1 = q2 = 1`, `η = 1` give
`s0 ≤ 27`, not the printed `61`. The exact value is 24, by Python. -/
theorem s0_example1_le : s0 nuAlg (√3) (-√2) 1 1 1 ≤ 27 := by
  have hl : |√3 * -√2| = √6 := by
    rw [mul_neg, abs_neg, abs_of_nonneg (by positivity), ← Real.sqrt_mul (by norm_num)]
    norm_num
  have h6 : √6 < 2.4495 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpos : 0 < 2 * Cq 1 1 * √6 := by
    have := Cq_one_one_pos; positivity
  have hnum : log (2 * Cq 1 1 * |√3 * -√2|) - log 1 ≤ 4 := by
    rw [hl, Real.log_one, sub_zero]
    apply le_of_lt
    rw [Real.log_lt_iff_lt_exp hpos]
    have h1 := Cq_one_one_lt
    have h2 : 2 * Cq 1 1 * √6 < 2 * 10.7151 * 2.4495 := by
      have := Cq_one_one_pos
      have : 0 ≤ √6 := Real.sqrt_nonneg 6
      nlinarith
    linarith [exp_four_gt]
  have hden := neg_log_ge (show (0 : ℝ) < nuAlg by norm_num [nuAlg])
  have := s0_le_of (A := 4) (B := 1 - nuAlg) (by norm_num [nuAlg]) (by norm_num) hnum hden
  have hc : ⌈(4 : ℝ) / (1 - nuAlg)⌉ ≤ 25 := by
    rw [Int.ceil_le]; norm_num [nuAlg]
  linarith

theorem s0_example1_ne : s0 nuAlg (√3) (-√2) 1 1 1 ≠ 61 := by
  have := s0_example1_le; omega

/-- **Example 2 under formula (2)**, with `q1 = q2 = 1` as the paper evidently took them:
`λ1 = π`, `λ2 = −√2`, `η = 1` give `s0 ≤ 60`, not the printed `119`. The exact value is 52,
by Python. Here `λ1/μ1 = π²` is irrational, outside the Theorem's hypotheses. -/
theorem s0_example2_le : s0 nuTr π (-√2) 1 1 1 ≤ 60 := by
  have hl : |π * -√2| = π * √2 := by
    rw [mul_neg, abs_neg, abs_of_nonneg (by positivity)]
  have h2 : √2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpi := Real.pi_lt_d2
  have hpos : 0 < 2 * Cq 1 1 * (π * √2) := by
    have := Cq_one_one_pos; positivity
  have hnum : log (2 * Cq 1 1 * |π * -√2|) - log 1 ≤ 5 := by
    rw [hl, Real.log_one, sub_zero]
    apply le_of_lt
    rw [Real.log_lt_iff_lt_exp hpos]
    have h1 := Cq_one_one_lt
    have hps : π * √2 < 3.15 * 1.4143 := by
      have : 0 ≤ √2 := Real.sqrt_nonneg 2
      nlinarith [Real.pi_pos]
    have h3 : 2 * Cq 1 1 * (π * √2) < 2 * 10.7151 * (3.15 * 1.4143) := by
      have := Cq_one_one_pos
      have : 0 ≤ π * √2 := by positivity
      nlinarith
    linarith [exp_five_gt]
  have hden := neg_log_ge (show (0 : ℝ) < nuTr by norm_num [nuTr])
  have := s0_le_of (A := 5) (B := 1 - nuTr) (by norm_num [nuTr]) (by norm_num) hnum hden
  have hc : ⌈(5 : ℝ) / (1 - nuTr)⌉ ≤ 58 := by
    rw [Int.ceil_le]; norm_num [nuTr]
  linarith

theorem s0_example2_ne : s0 nuTr π (-√2) 1 1 1 ≠ 119 := by
  have := s0_example2_le; omega

end LeanLab.LZPowersOfTwo
