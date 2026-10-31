import Mathlib

/-!
# Helfgott's book, Appendix A, Section A.1: closed forms of the smoothing norms

Unit U-6452, CLOUD 20261020T1318Z-cloud43, P0001 P0013. AI wrote this file.

Source: H. A. Helfgott, The ternary Goldbach problem, book draft of 2019-12-14, the version of
record per the author's reply in REPLIES.md, Appendix A, pages 506 to 513, copy
papers/P0001-book-AppA.pdf. With `η(x) = √(8/π) (e^{-x²/2} - e^{-2x²})`, display (A.2), and
`η₁(x) = √(2/π) x² e^{-x²/2}`, display (A.1):

* `eta_le` and `eta_xstar`: `|η|_∞ = 3/(2^{7/6} √π)`, attained at `x² = (4/3) log 2`, the value in
  (A.15); so `|η'|₁ = 2 |η|_∞ = 3/(2^{1/6} √π)`, `two_sup_eq`, the value in (A.15), since `η`
  rises from `η(0) = 0` to its one maximum and falls to `0`;
* `integral_eta`: `|η|₁ = ∫₀^∞ η = 1`, page 506;
* `eta1_le` and `eta1_sqrt2`: `max η₁ = η₁(√2) = √(2/π) · 2/e`, so `|η₁'|₁ = √32/(e √π)`,
  `two_eta1_max`, page 512.

The other printed constants of A.1, Lemmas A.1 to A.6, were recomputed at 30 digits in
gen/appA_U6452.py and .out, all MATCH; two cosmetic slips on pages 511 and 515 are recorded in
PROGRESS.md and FINDINGS.md. Known mathematics; these checks verify printed values only.
Ternary Goldbach is a theorem; binary Goldbach is OPEN.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace LeanLab.HelfgottArcs.BookAppA
open Real MeasureTheory Set

/-- Display (A.2), on all of `ℝ`; the book sets it to `0` for `x < 0`. -/
noncomputable def eta (x : ℝ) : ℝ := √(8 / π) * (exp (-x ^ 2 / 2) - exp (-2 * x ^ 2))

/-- Display (A.1) on `x ≥ 0`. -/
noncomputable def eta1 (x : ℝ) : ℝ := √(2 / π) * (x ^ 2 * exp (-x ^ 2 / 2))

/-- The quartic step: if `a³ = 1/4` then `u - u⁴ ≤ 3a/4` for every real `u`. -/
lemma quartic_le {a : ℝ} (ha0 : 0 < a) (ha : a ^ 3 = 1 / 4) (u : ℝ) : u - u ^ 4 ≤ 3 * a / 4 := by
  have key : 3 * a / 4 - (u - u ^ 4) = (u - a) ^ 2 * ((u + a) ^ 2 + 2 * a ^ 2) := by
    linear_combination (4 * u - 3 * a) * ha
  have : 0 ≤ (u - a) ^ 2 * ((u + a) ^ 2 + 2 * a ^ 2) := by positivity
  linarith

/-- `a = 2^{-2/3}`. -/
noncomputable def a0 : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ))

lemma a0_pos : 0 < a0 := rpow_pos_of_pos (by norm_num) _

lemma a0_cube : a0 ^ 3 = 1 / 4 := by
  unfold a0
  rw [← rpow_natCast, ← rpow_mul (by norm_num)]
  norm_num

lemma exp_sq_four (x : ℝ) : exp (-2 * x ^ 2) = exp (-x ^ 2 / 2) ^ 4 := by
  rw [← exp_nat_mul]; ring_nf

/-- The sup norm value of (A.15). -/
noncomputable def M : ℝ := 3 / ((2 : ℝ) ^ (7 / 6 : ℝ) * √π)

lemma M_eq : √(8 / π) * (3 * a0 / 4) = M := by
  have hπ : 0 < π := pi_pos
  have h8 : √(8 / π) = (2 : ℝ) ^ (3 / 2 : ℝ) / √π := by
    rw [sqrt_div' _ hπ.le]
    congr 1
    rw [sqrt_eq_rpow, show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← rpow_mul (by norm_num)]
    norm_num
  have h4 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
  have hs : 0 < √π := sqrt_pos.mpr hπ
  have hcomb : (2 : ℝ) ^ (3 / 2 : ℝ) * a0 / 4 = 1 / (2 : ℝ) ^ (7 / 6 : ℝ) := by
    unfold a0
    rw [h4, ← rpow_add (by norm_num), ← rpow_sub (by norm_num), one_div,
      ← rpow_neg (by norm_num)]
    norm_num
  rw [h8, M]
  have : (2 : ℝ) ^ (3 / 2 : ℝ) / √π * (3 * a0 / 4) = 3 * ((2 : ℝ) ^ (3 / 2 : ℝ) * a0 / 4) / √π := by
    ring
  rw [this, hcomb]
  have h76 : 0 < (2 : ℝ) ^ (7 / 6 : ℝ) := rpow_pos_of_pos (by norm_num) _
  field_simp

/-- **`η ≤ 3/(2^{7/6} √π)` everywhere**, the bound behind `|η|_∞` in (A.15). -/
theorem eta_le (x : ℝ) : eta x ≤ M := by
  rw [← M_eq, eta, exp_sq_four]
  exact mul_le_mul_of_nonneg_left (quartic_le a0_pos a0_cube _) (sqrt_nonneg _)

/-- The maximizer, `x*² = (4/3) log 2`. -/
noncomputable def xstar : ℝ := √(4 / 3 * Real.log 2)

lemma exp_xstar : exp (-xstar ^ 2 / 2) = a0 := by
  rw [xstar, sq_sqrt (by positivity), a0, rpow_def_of_pos (by norm_num)]
  congr 1; ring

/-- **The bound is attained**: `η(x*) = 3/(2^{7/6} √π)`, so `|η|_∞ = 3/(2^{7/6} √π)`. -/
theorem eta_xstar : eta xstar = M := by
  rw [← M_eq, eta, exp_sq_four, exp_xstar]
  congr 1
  have h := a0_cube
  linear_combination (-a0) * h

/-- `2 |η|_∞ = 3/(2^{1/6} √π)`, the printed `|η'|₁`. -/
theorem two_sup_eq : 2 * M = 3 / ((2 : ℝ) ^ (1 / 6 : ℝ) * √π) := by
  rw [M]
  have h : (2 : ℝ) ^ (7 / 6 : ℝ) = 2 * (2 : ℝ) ^ (1 / 6 : ℝ) := by
    rw [show (7 / 6 : ℝ) = 1 + 1 / 6 by norm_num, rpow_add (by norm_num), rpow_one]
  rw [h]
  have hs : 0 < √π := sqrt_pos.mpr pi_pos
  have h6 : 0 < (2 : ℝ) ^ (1 / 6 : ℝ) := rpow_pos_of_pos (by norm_num) _
  field_simp

/-- **`|η|₁ = 1`**: `∫₀^∞ η = 1`, page 506. -/
theorem integral_eta : ∫ x in Ioi (0 : ℝ), eta x = 1 := by
  have i1 : IntegrableOn (fun x : ℝ => exp (-(1 / 2) * x ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
  have i2 : IntegrableOn (fun x : ℝ => exp (-2 * x ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 2)).integrableOn
  have e : (fun x => eta x) = fun x => √(8 / π) * (exp (-(1 / 2) * x ^ 2) - exp (-2 * x ^ 2)) := by
    funext x; rw [eta]; congr 3; ring
  rw [e, integral_const_mul, integral_sub i1 i2, integral_gaussian_Ioi, integral_gaussian_Ioi]
  have hπ : 0 < π := pi_pos
  have s1 : √(8 / π) * √(π / (1 / 2)) = 4 := by
    rw [← sqrt_mul (by positivity), show 8 / π * (π / (1 / 2)) = 4 ^ 2 by field_simp; ring,
      sqrt_sq (by norm_num)]
  have s2 : √(8 / π) * √(π / 2) = 2 := by
    rw [← sqrt_mul (by positivity), show 8 / π * (π / 2) = 2 ^ 2 by field_simp; ring,
      sqrt_sq (by norm_num)]
  linear_combination s1 / 2 - s2 / 2

/-- `x² e^{-x²/2} ≤ 2/e`. -/
theorem sq_exp_le (x : ℝ) : x ^ 2 * exp (-x ^ 2 / 2) ≤ 2 / exp 1 := by
  set v := x ^ 2 / 2 with hv
  have h := add_one_le_exp (v - 1)
  have hx : x ^ 2 * exp (-x ^ 2 / 2) = 2 * (v * exp (-v)) := by rw [hv]; ring_nf
  rw [hx]
  have hev : exp (v - 1) = exp v / exp 1 := by rw [exp_sub]
  have hpos : 0 < exp v := exp_pos v
  have : v * exp (-v) ≤ 1 / exp 1 := by
    rw [exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hpos (exp_pos 1)]
    rw [hev, le_div_iff₀ (exp_pos 1)] at h
    nlinarith [exp_pos 1]
  have e2 : 2 / exp 1 = 2 * (1 / exp 1) := by ring
  linarith

/-- **`η₁ ≤ √(2/π) · 2/e`.** -/
theorem eta1_le (x : ℝ) : eta1 x ≤ √(2 / π) * (2 / exp 1) :=
  mul_le_mul_of_nonneg_left (sq_exp_le x) (sqrt_nonneg _)

/-- **Attained at `√2`.** -/
theorem eta1_sqrt2 : eta1 √2 = √(2 / π) * (2 / exp 1) := by
  rw [eta1, sq_sqrt (by norm_num)]
  congr 1
  rw [show -(2 : ℝ) / 2 = -1 by norm_num, exp_neg]; ring

/-- `2 max η₁ = √32/(e √π)`, the printed `|η₁'|₁`. -/
theorem two_eta1_max : 2 * (√(2 / π) * (2 / exp 1)) = √32 / (exp 1 * √π) := by
  have hπ : 0 < π := pi_pos
  have hs : 0 < √π := sqrt_pos.mpr hπ
  rw [sqrt_div' _ hπ.le, show (32 : ℝ) = 4 ^ 2 * 2 by norm_num, sqrt_mul (by positivity),
    sqrt_sq (by norm_num)]
  have := exp_pos 1
  field_simp
  ring

/-- Vacuity: `x* > 0`, so the maximizer is a point of `(0, ∞)` where (A.2) is the book's `η`. -/
theorem xstar_pos : 0 < xstar := by
  rw [xstar]; apply sqrt_pos.mpr; have := log_pos (by norm_num : (1 : ℝ) < 2); positivity

end LeanLab.HelfgottArcs.BookAppA
