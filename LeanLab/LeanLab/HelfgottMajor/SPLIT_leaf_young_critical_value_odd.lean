import Mathlib

/-!
Split of `leaf_young_critical_value_odd`, the core of Young 1913 as cited in Pomerance,
Remarks on the Pólya-Vinogradov inequality, Integers 11A 2011, section 2, proof of Lemma 2,
reference 16, also Pólya-Szegő Part VI Problem 27.

The derivative of `C_n x = sum_{j <= n} cos (j x) / j` is `- sum_{j <= n} sin (j x)`, and the
Lagrange identity `2 sin (x/2) sum_{j <= n} sin (j x) = 2 sin ((n+1) x / 2) sin (n x / 2)`,
proved here, locates the interior critical points on `0 < x < pi`: they are exactly the points
`x = 2 pi k / n` and `x = 2 pi k / (n+1)`. What remains is Young's evaluation of `C_n` at
these explicit points, left as two LEAFs.

No definition is introduced. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real Finset

/-- The telescoping form of the Lagrange identity:
`sum_{j <= n} 2 sin (x/2) sin (j x) = cos (x/2) - cos ((2n+1) x / 2)`. -/
theorem two_sin_half_mul_sum_sin (n : ℕ) (x : ℝ) :
    ∑ j ∈ Icc 1 n, 2 * sin (x / 2) * sin (j * x) = cos (x / 2) - cos ((2 * n + 1) * x / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    have e1 : (2 * (n : ℝ) + 1) * x / 2 = (n + 1) * x - x / 2 := by ring
    have e2 : (2 * ((n + 1 : ℕ) : ℝ) + 1) * x / 2 = (n + 1) * x + x / 2 := by push_cast; ring
    rw [e1, e2, cos_sub, cos_add]
    push_cast
    ring

/-- The Lagrange identity for the sine sum:
`2 sin (x/2) sum_{j <= n} sin (j x) = 2 sin ((n+1) x / 2) sin (n x / 2)`. -/
theorem two_sin_half_mul_sum_sin' (n : ℕ) (x : ℝ) :
    2 * sin (x / 2) * ∑ j ∈ Icc 1 n, sin (j * x) =
      2 * sin ((n + 1) * x / 2) * sin (n * x / 2) := by
  rw [mul_sum, two_sin_half_mul_sum_sin]
  have e1 : x / 2 = (n + 1) * x / 2 - n * x / 2 := by ring
  have e2 : (2 * (n : ℝ) + 1) * x / 2 = (n + 1) * x / 2 + n * x / 2 := by ring
  rw [e2, cos_add]
  conv_lhs => rw [e1, cos_sub]
  ring

/-- LEAF: Young 1913, Pólya-Szegő Part VI Problem 27, the value of
`C_n x = sum_{j <= n} cos (j x) / j` at the critical points `x = 2 pi k / n`, the zeros of
`sin (n x / 2)` in `0 < x < pi`, for odd `n`: it is at least `C_n pi`.
HARD: Young's evaluation at an explicit critical point. -/
theorem leaf_young_value_at_two_pi_k_div_n (n : ℕ) (hn : Odd n) (k : ℤ) (hk0 : 0 < k)
    (hkn : 2 * k < n) :
    ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ j / (j : ℝ) ≤
      ∑ j ∈ Icc 1 n, cos (j * (2 * π * k / n)) / (j : ℝ) := by
  sorry

/-- LEAF: Young 1913, Pólya-Szegő Part VI Problem 27, the value of
`C_n x = sum_{j <= n} cos (j x) / j` at the critical points `x = 2 pi k / (n+1)`, the zeros of
`sin ((n+1) x / 2)` in `0 < x < pi`, for odd `n`: it is at least `C_n pi`.
HARD: Young's evaluation at an explicit critical point. -/
theorem leaf_young_value_at_two_pi_k_div_n_succ (n : ℕ) (hn : Odd n) (k : ℤ) (hk0 : 0 < k)
    (hkn : 2 * k < n + 1) :
    ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ j / (j : ℝ) ≤
      ∑ j ∈ Icc 1 n, cos (j * (2 * π * k / (n + 1))) / (j : ℝ) := by
  sorry

/-- The interior critical points of `C_n` on `0 < x < pi` are the points `2 pi k / n` and
`2 pi k / (n+1)`, by the Lagrange identity; so Young's critical value bound follows from the two
LEAFs above. -/
theorem young_critical_value_odd_of_leaves (n : ℕ) (hn : Odd n) (x : ℝ) (hx0 : 0 < x)
    (hxpi : x < π) (hcrit : ∑ j ∈ Icc 1 n, sin (j * x) = 0) :
    ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ j / (j : ℝ) ≤ ∑ j ∈ Icc 1 n, cos (j * x) / (j : ℝ) := by
  have hL := two_sin_half_mul_sum_sin' n x
  rw [hcrit, mul_zero] at hL
  have hprod : sin ((n + 1) * x / 2) * sin (n * x / 2) = 0 := by linarith
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := hn.pos
    exact_mod_cast this
  rcases mul_eq_zero.1 hprod with h | h
  · obtain ⟨k, hk⟩ := sin_eq_zero_iff.1 h
    have hx : x = 2 * π * k / (n + 1) := by
      field_simp; linarith
    have hk0 : (0 : ℝ) < k := by
      have : 0 < (k : ℝ) * π := by rw [hk]; positivity
      exact pos_of_mul_pos_left this pi_pos.le
    have hkn : (2 * k : ℝ) < n + 1 := by
      have : (k : ℝ) * π < (n + 1) * π / 2 := by
        rw [hk]; nlinarith [pi_pos]
      nlinarith [pi_pos]
    have hk0' : 0 < k := by exact_mod_cast hk0
    have hkn' : 2 * k < n + 1 := by exact_mod_cast hkn
    rw [hx]
    exact leaf_young_value_at_two_pi_k_div_n_succ n hn k hk0' hkn'
  · obtain ⟨k, hk⟩ := sin_eq_zero_iff.1 h
    have hx : x = 2 * π * k / n := by
      field_simp; linarith
    have hk0 : (0 : ℝ) < k := by
      have : 0 < (k : ℝ) * π := by rw [hk]; positivity
      exact pos_of_mul_pos_left this pi_pos.le
    have hkn : (2 * k : ℝ) < n := by
      have : (k : ℝ) * π < n * π / 2 := by
        rw [hk]; nlinarith [pi_pos]
      nlinarith [pi_pos]
    have hk0' : 0 < k := by exact_mod_cast hk0
    have hkn' : 2 * k < n := by exact_mod_cast hkn
    rw [hx]
    exact leaf_young_value_at_two_pi_k_div_n n hn k hk0' hkn'

end LeanLab.HelfgottMajor.PolyaVinogradov123
