import LeanLab.HelfgottMajor.BookT143Eps
import LeanLab.HelfgottMajor.BookT143Fix

/-!
P0014 book Part IV, pages 444 and 448 to 451, display 16.60.
This joins the two pieces named by the last pre-task progress entry.
The final estimates are CONDITIONAL ON the stated envelope of Proposition 16.19.
The constants retain the existing repairs in BookT143Fix.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.BookComplete123
open Real
open LeanLab.HelfgottMajor.BookE
open LeanLab.HelfgottMajor.BookT143Eps
open LeanLab.HelfgottMajor.BookT143Fix

/-- The first line of display 16.60, with log qT replaced by the upper cap log A. -/
noncomputable def tail (K δ A : ℝ) : ℝ :=
  let T0 := K * max |δ| 4
  let r := T0 / (π ^ 2 * δ ^ 2)
  (max 1.05 (2.72 * (1 / sqrt r)) * exp (-(E r * T0)) +
    0.75 * exp (-(π / 4) * T0)) * log (A / (2 * π))

/-- The remaining lines of display 16.60, with the same cap log A. -/
noncomputable def remainder (K H A x q δ : ℝ) : ℝ :=
  ((0.566 * log A + 1.41) * sqrt (K * max |δ| 4 + H) +
    (0.84 * log q + 11.52)) * sqrt x + (1.6 * |δ| + 1.1) +
      6.1 * log q * (6 + 2 * |δ|) / sqrt x

/-- The qT cap used on book pages 448 and 450. -/
theorem qT_cap {K H q Q C δ : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H) (hq : 0 < q)
    (hQ : q ≤ Q) (hC : 4 * Q ≤ C) (hδ : |δ| ≤ C / q) :
    q * (K * max |δ| 4 + H) ≤ K * C + H * Q := by
  have hdq : |δ| * q ≤ C := (le_div_iff₀ hq).mp hδ
  have hm : q * max |δ| 4 ≤ C := by
    rcases le_total 4 |δ| with h | h
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right h]
      nlinarith
  have h1 := mul_le_mul_of_nonneg_left hm hK
  have h2 := mul_le_mul_of_nonneg_left hQ hH
  nlinarith

/-- Book Theorem 14.3 part 1, full error assembly for nonzero delta.
CONDITIONAL ON the capped max envelope hP of Proposition 16.19 on page 444.
The two forms use the existing repaired square-root coefficients from pages 448 and 449.
-/
theorem complete_p1 {S x q δ : ℝ} (hx : 1e6 ≤ x) (hq1 : 1 ≤ q) (hq : q ≤ 400000)
    (hδ : δ ≠ 0) (hb : |δ| ≤ 1.6e6)
    (hP : S ≤ tail (1375 / 32) δ 108750000 * x +
      remainder (1375 / 32) 100 108750000 x q δ) :
    S ≤ 1.93e-6 * x + (98 * sqrt (max |δ| 4) + 23) * sqrt x + 2 * |δ| ∧
    S ≤ 1.93e-6 * x + (78 * sqrt (max |δ| 4) + 68) * sqrt x + 2 * |δ| := by
  have he := eps_p1_delta hδ hb
  rw [T0_p1_eq] at he
  change tail (1375 / 32) δ 108750000 ≤ 1.93e-6 at he
  have hr := thm143_p1_fixed (D := max |δ| 4) hx hq1 hq (abs_nonneg δ) (le_max_right _ _)
  change remainder (1375 / 32) 100 108750000 x q δ ≤
      (98 * sqrt (max |δ| 4) + 23) * sqrt x + 2 * |δ| ∧
    remainder (1375 / 32) 100 108750000 x q δ ≤
      (78 * sqrt (max |δ| 4) + 68) * sqrt x + 2 * |δ| at hr
  have ht := mul_le_mul_of_nonneg_right he (by linarith : 0 ≤ x)
  constructor <;> linarith [hr.1, hr.2]

/-- Book Theorem 14.3 part 2, full error assembly for nonzero delta.
CONDITIONAL ON the capped max envelope hP of Proposition 16.19 on page 444.
The exponential coefficient is the existing repaired value from page 450.
-/
theorem complete_p2 {S x q δ : ℝ} (hx : 1e6 ≤ x) (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hδ : δ ≠ 0) (hb : |δ| ≤ 6e5)
    (hP : S ≤ tail (125 / 2) δ 1.35e8 * x + remainder (125 / 2) 200 1.35e8 x q δ) :
    S ≤ 3.05e-17 * x + (127.4 * sqrt (max |δ| 4) + 23) * sqrt x + 2 * |δ| ∧
    S ≤ 3.05e-17 * x + (95 * sqrt (max |δ| 4) + 99) * sqrt x + 2 * |δ| := by
  have he := eps_p2_delta hδ hb
  rw [T0_p2_eq] at he
  change tail (125 / 2) δ 1.35e8 ≤ 3.05e-17 at he
  have hr := thm143_p2_fixed (D := max |δ| 4) hx hq1 hq (abs_nonneg δ) (le_max_right _ _)
  change remainder (125 / 2) 200 1.35e8 x q δ ≤
      (127.4 * sqrt (max |δ| 4) + 23) * sqrt x + 2 * |δ| ∧
    remainder (125 / 2) 200 1.35e8 x q δ ≤
      (95 * sqrt (max |δ| 4) + 99) * sqrt x + 2 * |δ| at hr
  have ht := mul_le_mul_of_nonneg_right he (by linarith : 0 ≤ x)
  constructor <;> linarith [hr.1, hr.2]

end LeanLab.HelfgottMajor.BookComplete123
