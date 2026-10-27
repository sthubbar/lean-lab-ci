/-
P0080 Hathi 2021, arXiv 2109.13174v3, the small inequalities behind the bounds on `c_{4,P}`,
page 6, and on `c₃` and `c₃'`, pages 10-11, display (3.9).
Unit U-6151, CLOUD 20261020T0717Z-cloud37. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

* page 6: `1 + a(p)/(p - 1)⁴ ≤ 1 + 3.1/p²` for `p ≥ 103`; the threshold is sharp among primes,
  the inequality fails at `p = 101 ≡ 1 mod 4`.
* (3.9): with `1 + ε(p) = (1 + 1/c(p))/(1 + 1/(p - 1))`, `ε(p) ≤ 7.44/p²`. The paper states it
  for `p ≥ 742`; it holds for every `p ≥ 11` in both classes mod 4, and fails at `p = 7`.
  So the printed range is correct and loose; no effect on any result.
* the comparison `1 + k y ≤ (1 - y)^{-k}` used with `k = 3.1` and `k = 7.44`.
* page 11: `c₃' = (1 - 1/101)(1 - 1/107)(1 - 1/131) < 0.97336`.
KNOWN mathematics; these check printed constants.
-/
import Mathlib

namespace LeanLab.Hathi2021.Lemma31Consts
open Real

/-- Page 6, `p ≡ 1 mod 4`: `a(p)/(p - 1)⁴ = (3p + 1)/(p - 1)³ ≤ 3.1/p²` for `p ≥ 103`. -/
theorem a_le_31 (p : ℝ) (hp : 103 ≤ p) :
    (3 * p + 1) * (p - 1) / (p - 1) ^ 4 ≤ (31 / 10) / p ^ 2 := by
  have hq : (0 : ℝ) < p - 1 := by linarith
  rw [div_le_div_iff₀ (pow_pos hq 4) (by positivity)]
  have hd : 31 * (p - 1) ^ 3 - 10 * (3 * p + 1) * p ^ 2 ≥ 0 := by
    have ht : (0 : ℝ) ≤ p - 103 := by linarith
    have : 31 * (p - 1) ^ 3 - 10 * (3 * p + 1) * p ^ 2 =
        (p - 103) ^ 3 + 206 * (p - 103) ^ 2 + 10702 * (p - 103) + 9548 := by ring
    rw [this]; positivity
  have : (31 / 10) * (p - 1) ^ 4 - (3 * p + 1) * (p - 1) * p ^ 2 =
      (p - 1) / 10 * (31 * (p - 1) ^ 3 - 10 * (3 * p + 1) * p ^ 2) := by ring
  nlinarith [mul_nonneg hq.le hd]

/-- The threshold 103 is sharp among primes `≡ 1 mod 4`: the inequality fails at `p = 101`. -/
theorem a_le_31_fails_101 : ¬ ((3 * 101 + 1) * (101 - 1) / (101 - 1) ^ 4 ≤ (31 / 10) / (101 : ℝ) ^ 2) := by
  norm_num

/-- For `p ≡ 3 mod 4`, `a(p) < 0`, so page 6's bound holds for every such `p`. -/
theorem a_neg_3mod4 (p : ℝ) (hp : 1 < p) : -(p + 1) ^ 2 / (p - 1) ^ 4 ≤ (31 / 10) / p ^ 2 := by
  have : -(p + 1) ^ 2 / (p - 1) ^ 4 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
  have : 0 ≤ (31 / 10) / p ^ 2 := by positivity
  linarith

/-- `1 + k y ≤ (1 - y)^{-k}` for `0 ≤ y < 1`, `k ≥ 0`, the comparison with `ζ(2)` on pages 6
and 11. -/
theorem one_add_le_rpow (k y : ℝ) (hk : 0 ≤ k) (_hy0 : 0 ≤ y) (hy1 : y < 1) :
    1 + k * y ≤ (1 - y) ^ (-k) := by
  have h1 : 0 < 1 - y := by linarith
  rw [Real.rpow_def_of_pos h1]
  have hl : Real.log (1 - y) ≤ -y := by
    have := Real.log_le_sub_one_of_pos h1; linarith
  calc 1 + k * y ≤ Real.exp (k * y) := by
        have := Real.add_one_le_exp (k * y); linarith
    _ ≤ Real.exp (Real.log (1 - y) * -k) := by
        apply Real.exp_le_exp.mpr; nlinarith

/-- `1 + ε(p)` for `p ≡ 1 mod 4`, with `b(p) = (p - 1)(p² + 6p + 1)` and `a(p) = (3p + 1)(p - 1)`,
pages 5 and 11, written with `q = p - 1`. -/
noncomputable def onePlusEps1 (p : ℝ) : ℝ :=
  (1 + (p - 1) * (p ^ 2 + 6 * p + 1) / (p - 1) ^ 4) / (1 + (3 * p + 1) * (p - 1) / (p - 1) ^ 4) /
    (1 + 1 / (p - 1))

/-- `1 + ε(p)` for `p ≡ 3 mod 4`, with `b(p) = (p - 1)(p + 1)²` and `a(p) = -(p + 1)²`. -/
noncomputable def onePlusEps3 (p : ℝ) : ℝ :=
  (1 + (p - 1) * (p + 1) ^ 2 / (p - 1) ^ 4) / (1 + -(p + 1) ^ 2 / (p - 1) ^ 4) /
    (1 + 1 / (p - 1))

lemma eps_form (p A B : ℝ) (hp : 2 ≤ p) (hA : 0 < (p - 1) ^ 4 + A) :
    (1 + B / (p - 1) ^ 4) / (1 + A / (p - 1) ^ 4) / (1 + 1 / (p - 1)) =
      ((p - 1) ^ 4 + B) * (p - 1) / (((p - 1) ^ 4 + A) * p) := by
  have hq : (p - 1) ≠ 0 := by intro h; linarith
  have hq4 : (p - 1) ^ 4 ≠ 0 := pow_ne_zero 4 hq
  have hp0 : p ≠ 0 := by intro h; linarith
  have h1 : 1 + A / (p - 1) ^ 4 = ((p - 1) ^ 4 + A) / (p - 1) ^ 4 := by field_simp
  have h2 : 1 + B / (p - 1) ^ 4 = ((p - 1) ^ 4 + B) / (p - 1) ^ 4 := by field_simp
  have h3 : 1 + 1 / (p - 1) = p / (p - 1) := by field_simp; ring
  rw [h1, h2, h3]
  field_simp

/-- **(3.9), `p ≡ 1 mod 4`: `ε(p) ≤ 7.44/p²` for every `p ≥ 11`**, so for the printed `p ≥ 742`. -/
theorem eps1_le (p : ℝ) (hp : 11 ≤ p) : onePlusEps1 p ≤ 1 + (744 / 100) / p ^ 2 := by
  have hq : (0 : ℝ) < p - 1 := by linarith
  have hA : 0 < (p - 1) ^ 4 + (3 * p + 1) * (p - 1) := by positivity
  unfold onePlusEps1
  rw [eps_form p _ _ (by linarith) hA, div_le_iff₀ (by positivity)]
  have ht : (0 : ℝ) ≤ p - 11 := by linarith
  have hd : 100 * ((1 + (744 / 100) / p ^ 2) * (((p - 1) ^ 4 + (3 * p + 1) * (p - 1)) * p) -
      ((p - 1) ^ 4 + (p - 1) * (p ^ 2 + 6 * p + 1)) * (p - 1)) * p =
      244 * (p - 11) ^ 4 + 9160 * (p - 11) ^ 3 + 130932 * (p - 11) ^ 2 + 850016 * (p - 11)
        + 2126960 := by
    field_simp; ring
  have hpos : 0 ≤ 244 * (p - 11) ^ 4 + 9160 * (p - 11) ^ 3 + 130932 * (p - 11) ^ 2 +
      850016 * (p - 11) + 2126960 := by positivity
  rw [← hd] at hpos
  have hp0 : 0 < 100 * p := by linarith
  nlinarith

/-- **(3.9), `p ≡ 3 mod 4`: `ε(p) ≤ 7.44/p²` for every `p ≥ 11`.** -/
theorem eps3_le (p : ℝ) (hp : 11 ≤ p) : onePlusEps3 p ≤ 1 + (744 / 100) / p ^ 2 := by
  have hq : (0 : ℝ) < p - 1 := by linarith
  have hA : 0 < (p - 1) ^ 4 + -(p + 1) ^ 2 := by
    have h1 : 100 ≤ (p - 1) ^ 2 := by nlinarith
    have h2 : (p - 1) ^ 4 = ((p - 1) ^ 2) ^ 2 := by ring
    have h3 : (p + 1) ^ 2 ≤ 4 * (p - 1) ^ 2 := by nlinarith
    nlinarith
  unfold onePlusEps3
  rw [eps_form p _ _ (by linarith) hA, div_le_iff₀ (by nlinarith)]
  have hd : 100 * ((1 + (744 / 100) / p ^ 2) * (((p - 1) ^ 4 + -(p + 1) ^ 2) * p) -
      ((p - 1) ^ 4 + (p - 1) * (p + 1) ^ 2) * (p - 1)) * p =
      244 * (p - 11) ^ 4 + 8360 * (p - 11) ^ 3 + 101956 * (p - 11) ^ 2 + 502944 * (p - 11)
        + 750464 := by
    field_simp; ring
  have ht : (0 : ℝ) ≤ p - 11 := by linarith
  have hpos : 0 ≤ 244 * (p - 11) ^ 4 + 8360 * (p - 11) ^ 3 + 101956 * (p - 11) ^ 2 +
      502944 * (p - 11) + 750464 := by positivity
  rw [← hd] at hpos
  have hp0 : 0 < 100 * p := by linarith
  nlinarith

/-- (3.9) fails at `p = 7 ≡ 3 mod 4`: `ε(7) = 8.27…/49 > 7.44/49`. So `p ≥ 11` is the true range
among primes above 5. -/
theorem eps3_fails_7 : ¬ (onePlusEps3 7 ≤ 1 + (744 / 100) / (7 : ℝ) ^ 2) := by
  unfold onePlusEps3; norm_num

/-- **Page 10: `c(p) < p - 1`**, that is `1 + ε(p) > 1`, for `p ≡ 1 mod 4`, every `p ≥ 5`.
The difference `(q⁴ + b)q - (q⁴ + a)p` is `5p³ - 14p² + 9p`. -/
theorem eps1_pos (p : ℝ) (hp : 5 ≤ p) : 1 < onePlusEps1 p := by
  have hq : (0 : ℝ) < p - 1 := by linarith
  have hA : 0 < (p - 1) ^ 4 + (3 * p + 1) * (p - 1) := by positivity
  unfold onePlusEps1
  rw [eps_form p _ _ (by linarith) hA, lt_div_iff₀ (by positivity)]
  have : ((p - 1) ^ 4 + (p - 1) * (p ^ 2 + 6 * p + 1)) * (p - 1) -
      ((p - 1) ^ 4 + (3 * p + 1) * (p - 1)) * p = 5 * (p - 5) ^ 3 + 61 * (p - 5) ^ 2 + 244 * (p - 5) + 320 := by
    ring
  have ht : (0 : ℝ) ≤ p - 5 := by linarith
  have : (0 : ℝ) < 5 * (p - 5) ^ 3 + 61 * (p - 5) ^ 2 + 244 * (p - 5) + 320 := by positivity
  linarith

/-- **Page 10: `c(p) < p - 1`** for `p ≡ 3 mod 4`, every `p ≥ 7`; at `p = 3` the factor
`1 + a(3)/2⁴` is `0`, and 3 is in `P`. The difference is `5p³ - 6p² + 5p`. -/
theorem eps3_pos (p : ℝ) (hp : 7 ≤ p) : 1 < onePlusEps3 p := by
  have hq : (0 : ℝ) < p - 1 := by linarith
  have hA : 0 < (p - 1) ^ 4 + -(p + 1) ^ 2 := by
    have h1 : 36 ≤ (p - 1) ^ 2 := by nlinarith
    have h2 : (p - 1) ^ 4 = ((p - 1) ^ 2) ^ 2 := by ring
    have h3 : (p + 1) ^ 2 ≤ 4 * (p - 1) ^ 2 := by nlinarith
    nlinarith
  unfold onePlusEps3
  rw [eps_form p _ _ (by linarith) hA, lt_div_iff₀ (by nlinarith)]
  have : ((p - 1) ^ 4 + (p - 1) * (p + 1) ^ 2) * (p - 1) -
      ((p - 1) ^ 4 + -(p + 1) ^ 2) * p = 5 * (p - 7) ^ 3 + 99 * (p - 7) ^ 2 + 656 * (p - 7) + 1456 := by
    ring
  have ht : (0 : ℝ) ≤ p - 7 := by linarith
  have : (0 : ℝ) < 5 * (p - 7) ^ 3 + 99 * (p - 7) ^ 2 + 656 * (p - 7) + 1456 := by positivity
  linarith

/-- **Page 11: `c₃' < 0.97336`.** -/
theorem c3prime_lt : (1 - 1 / 101 : ℝ) * (1 - 1 / 107) * (1 - 1 / 131) < 97336 / 100000 := by
  norm_num

end LeanLab.Hathi2021.Lemma31Consts
