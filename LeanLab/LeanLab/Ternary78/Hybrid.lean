/-
I-0086, T2 FRONTIER, MODEL: Radziwiłł's hybrid, a zero-free half-plane `Re s > 7/8` on the major
arcs with Helfgott's unconditional minor arcs, against the Helfgott-Platt check to `8.875·10³⁰`.

MODEL, not a theorem about the circle method: Helfgott's minor arcs need major arcs up to
`q ≤ 2 r₀ = 300000`, and Section 7.4 of arXiv 1312.7748 v2 leaves a relative margin
`m = 0.08433 / 1.058298 = 0.07968` between the major arc main term `1.058298 x²/κ` and
the minor arc bound `0.97392 x²/κ`, Helfgott2013/Chain.lean. Under `Re s ≤ 7/8` the explicit
formula bounds the relative major arc error at `a/q` by `S √q x^{-1/8}`, `√q` from the Gauss
sum and `S` the weighted sum over zeros. The hybrid closes only if `S √q x^{-1/8} ≤ m` at
`q = 300000`.

* `hybrid_fails`: `m x^{1/8} < S √Q` whenever `m⁸ x < S⁸ Q⁴`.
* `hybrid_fails_generous`: with `S = 1`, the most generous model, it fails for every
  `x ≤ 4.4·10³⁰`, that is `N ≤ 8.88·10³⁰` with `x = 0.495461 N`; the threshold is
  `x = 4.98·10³⁰`, `N = 1.006·10³¹`, just above the Helfgott-Platt check.
* `hybrid_fails_S2`: with `S = 2` it fails for every `x ≤ 1.27·10³³`, `N ≤ 2.5·10³³`.

AI-written Lean code, Claude, PC run 20261020T0403Z-27388, unit U-1161. Real-number facts only;
the circle method link is a MODEL. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Ternary78.Hybrid
open Real

/-- The relative margin of Helfgott's Section 7.4: `0.08433 / 1.058298`. -/
noncomputable def margin : ℝ := 0.08433 / 1.058298

lemma margin_bounds : (0.079684 : ℝ) < margin ∧ margin < 0.079685 := by
  unfold margin; constructor <;> norm_num

/-- **The hybrid fails** at `x` when `m⁸ x < S⁸ Q⁴`: then `m x^{1/8} < S √Q`, so the major arc
error `S √Q x^{-1/8}` exceeds the margin `m`. -/
theorem hybrid_fails {Q S m x : ℝ} (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hm : 0 < m) (hx : 0 < x)
    (h : m ^ 8 * x < S ^ 8 * Q ^ 4) : m * x ^ (1 / 8 : ℝ) < S * sqrt Q := by
  have hy : 0 ≤ x ^ (1 / 8 : ℝ) := rpow_nonneg hx.le _
  have hy8 : (x ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = x := by
    rw [← rpow_natCast, ← rpow_mul hx.le]; norm_num
  have hq8 : (sqrt Q) ^ (8 : ℕ) = Q ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, sq_sqrt hQ]
  have lhs : (m * x ^ (1 / 8 : ℝ)) ^ 8 = m ^ 8 * x := by rw [mul_pow, hy8]
  have rhs : (S * sqrt Q) ^ 8 = S ^ 8 * Q ^ 4 := by rw [mul_pow, hq8]
  have h8 : (m * x ^ (1 / 8 : ℝ)) ^ 8 < (S * sqrt Q) ^ 8 := by rw [lhs, rhs]; exact h
  exact lt_of_pow_lt_pow_left₀ 8 (mul_nonneg hS (sqrt_nonneg _)) h8

/-- **Generous model, `S = 1`**: the hybrid fails for every `0 < x ≤ 4.4·10³⁰`. -/
theorem hybrid_fails_generous {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 4.4e30) :
    margin * x ^ (1 / 8 : ℝ) < 1 * sqrt 300000 := by
  refine hybrid_fails (by norm_num) (by norm_num) (by unfold margin; norm_num) hx ?_
  have hm8 : margin ^ 8 ≤ (0.079685 : ℝ) ^ 8 :=
    pow_le_pow_left₀ (by unfold margin; norm_num) margin_bounds.2.le 8
  calc margin ^ 8 * x ≤ (0.079685 : ℝ) ^ 8 * 4.4e30 :=
        mul_le_mul hm8 hx2 hx.le (by positivity)
    _ < 1 ^ 8 * 300000 ^ 4 := by norm_num

/-- **`S = 2`**: the hybrid fails for every `0 < x ≤ 1.27·10³³`. -/
theorem hybrid_fails_S2 {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 1.27e33) :
    margin * x ^ (1 / 8 : ℝ) < 2 * sqrt 300000 := by
  refine hybrid_fails (by norm_num) (by norm_num) (by unfold margin; norm_num) hx ?_
  have hm8 : margin ^ 8 ≤ (0.079685 : ℝ) ^ 8 :=
    pow_le_pow_left₀ (by unfold margin; norm_num) margin_bounds.2.le 8
  calc margin ^ 8 * x ≤ (0.079685 : ℝ) ^ 8 * 1.27e33 :=
        mul_le_mul hm8 hx2 hx.le (by positivity)
    _ < 2 ^ 8 * 300000 ^ 4 := by norm_num

/-- Vacuity: `x = 4.4·10³⁰`, that is `N = 8.88·10³⁰`, meets the hypotheses. -/
example : margin * (4.4e30 : ℝ) ^ (1 / 8 : ℝ) < 1 * sqrt 300000 :=
  hybrid_fails_generous (by norm_num) le_rfl

#print axioms hybrid_fails
#print axioms hybrid_fails_generous
#print axioms hybrid_fails_S2

end LeanLab.Ternary78.Hybrid
