import LeanLab.RieselVaughan1983.Lemma6Theta

/-!
Supply for the initial Dusart theta leaf in DecompJ206.
Dusart 2010 Theorem 5.2 uses finite computation at the initial endpoint.
Table 6.3 supplies the later relative errors. Proposition 5.1 supplies the upper sign.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Chebyshev

namespace LeanLab.RieselVaughan1983.Task426

/-- LEAF. Dusart 2010 page 4, Proposition 5.1.
Only the initial band with log x from 22 to 27 is required.
This is a one-sided relative upper bound, not the target absolute logarithmic bound. -/
theorem dusart_initial_upper (x : ℝ) (hx : 0 < x) (h22 : 22 ≤ log x)
    (h27 : log x < 27) :
    θ x - x < x / 36260 := by
  sorry

/-- LEAF. Dusart 2010 pages 4 and 5, Theorem 5.2, k = 1, eta = 0.001.
Only the lower sign on the bounded band from exp 22 to exp 27 remains here.
The upper sign and all larger arguments are separate obligations. -/
theorem dusart_initial_lower (x : ℝ) (hx : 0 < x) (h22 : 22 ≤ log x)
    (h27 : log x < 27) :
    -(1 / 1000 : ℝ) * x / log x < θ x - x := by
  sorry

/-- LEAF. Dusart 2010 page 15, Table 6.3, theta column at b = 27, 28, 32, 100.
Each estimate is restricted to a bounded interval ending at u.
The conversion to the logarithmic error budget is proved below. -/
theorem dusart_theta_relative_rows (b u ε x : ℝ)
    (hrow : (b, u, ε) ∈
      ([(27, 28, 3507 / 100000000), (28, 32, 2308 / 100000000),
        (32, 100, 4057 / 1000000000), (100, 300, 2903 / 100000000000000)] :
        List (ℝ × ℝ × ℝ)))
    (hx : 0 < x) (hb : b ≤ log x) (hu : log x ≤ u) :
    |θ x - x| < ε * x := by
  sorry

/-- Relative error conversion used for the four selected Table 6.3 rows.
The coefficient budget is explicit and no cited result is used. -/
theorem theta_log_error_of_relative {x ε u : ℝ} (hx : 0 < x) (hL : 0 < log x)
    (hu : log x ≤ u) (hε : 0 ≤ ε) (hbudget : ε * u ≤ 1 / 1000)
    (herror : |θ x - x| < ε * x) :
    |θ x - x| < (1 / 1000 : ℝ) * x / log x := by
  apply (lt_div_iff₀ hL).mpr
  have hmul := mul_lt_mul_of_pos_right herror hL
  have hcoef : ε * log x ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_left hu hε).trans hbudget
  have hscaled := mul_le_mul_of_nonneg_right hcoef hx.le
  nlinarith

/-- Initial-band absolute error from its separate upper and lower estimates.
CONDITIONAL ON the two displayed pointwise estimates, with clean axioms. -/
theorem dusart_initial_of_signed {x : ℝ} (hx : 0 < x) (h22 : 22 ≤ log x)
    (h27 : log x < 27) (hupper : θ x - x < x / 36260)
    (hlower : -(1 / 1000 : ℝ) * x / log x < θ x - x) :
    |θ x - x| < (1 / 1000 : ℝ) * x / log x := by
  have hL : 0 < log x := by linarith
  apply abs_lt.mpr
  constructor
  · simpa only [neg_div, neg_mul] using hlower
  · have hbudget : x / 36260 < (1 / 1000 : ℝ) * x / log x := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 36260) hL]
      nlinarith [mul_pos hx (show (0 : ℝ) < 27 - log x by linarith)]
    exact hupper.trans hbudget

/-- Exact supply statement for Task246.dusart_theta_initial_leaf.
CONDITIONAL ON the two initial signed estimates and four selected relative table rows.
The sealed source file is unchanged. -/
theorem dusart_theta_initial_supply (x : ℝ) (hx0 : 0 < x) (hx22 : 22 ≤ log x)
    (hx300 : log x < 300) :
    |θ x - x| < (1 / 1000) * x / log x := by
  by_cases h27 : log x < 27
  · exact dusart_initial_of_signed hx0 hx22 h27
      (dusart_initial_upper x hx0 hx22 h27) (dusart_initial_lower x hx0 hx22 h27)
  have hL : 0 < log x := by linarith
  have h27le : 27 ≤ log x := le_of_not_gt h27
  by_cases h28 : log x ≤ 28
  · apply theta_log_error_of_relative hx0 hL h28 (by norm_num)
      (by norm_num : (3507 / 100000000 : ℝ) * 28 ≤ 1 / 1000)
    exact dusart_theta_relative_rows 27 28 _ x (by simp) hx0 h27le h28
  by_cases h32 : log x ≤ 32
  · apply theta_log_error_of_relative hx0 hL h32 (by norm_num)
      (by norm_num : (2308 / 100000000 : ℝ) * 32 ≤ 1 / 1000)
    exact dusart_theta_relative_rows 28 32 _ x (by simp) hx0 (by linarith) h32
  by_cases h100 : log x ≤ 100
  · apply theta_log_error_of_relative hx0 hL h100 (by norm_num)
      (by norm_num : (4057 / 1000000000 : ℝ) * 100 ≤ 1 / 1000)
    exact dusart_theta_relative_rows 32 100 _ x (by simp) hx0 (by linarith) h100
  apply theta_log_error_of_relative hx0 hL hx300.le (by norm_num)
    (by norm_num : (2903 / 100000000000000 : ℝ) * 300 ≤ 1 / 1000)
  exact dusart_theta_relative_rows 100 300 _ x (by simp) hx0 (by linarith) hx300.le

/-- The shared Dusart k = 2 input already gives the requested logarithmic
error on the whole tail from log x equal to 27. CONDITIONAL ON that cited input.
Source: Dusart 2010 page 4, Theorem 5.2, eta_2 = 0.01. -/
theorem dusart_tail_of_k2 (hD : LeanLab.Common.ThetaWindow.DusartThm52k2)
    (x : ℝ) (hx0 : 0 < x) (hx27 : 27 ≤ log x) :
    |θ x - x| < (1 / 1000 : ℝ) * x / log x := by
  have hthreshold : (7713133853 : ℝ) ≤ exp 23 := by
    have h := Lemma6Theta.exp_nat_ge 23
    norm_num at h
    linarith
  have h23 : exp (23 : ℝ) ≤ x := (le_log_iff_exp_le hx0).mp (by linarith)
  have herror := hD x (hthreshold.trans h23)
  have hL : 0 < log x := by linarith
  have hbudget : (0.01 : ℝ) * x / log x ^ 2 < (1 / 1000 : ℝ) * x / log x := by
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < log x ^ 2) hL]
    have hp := mul_pos hx0 (show 0 < (1 / 1000 : ℝ) * log x - 0.01 by linarith)
    have hpL := mul_pos hp hL
    nlinarith
  exact herror.trans_lt hbudget

/-- An alternative exact theta conclusion from the two initial signed inputs
and the already shared k = 2 source, without a new table input.
CONDITIONAL ON the three explicitly supplied analytic inputs.
Source: Dusart 2010 pages 4 and 5, Theorem 5.2 and Proposition 5.1. -/
theorem dusart_initial_of_signed_and_k2
    (hD : LeanLab.Common.ThetaWindow.DusartThm52k2)
    (hupper : ∀ x : ℝ, 0 < x → 22 ≤ log x → log x < 27 → θ x - x < x / 36260)
    (hlower : ∀ x : ℝ, 0 < x → 22 ≤ log x → log x < 27 →
      -(1 / 1000 : ℝ) * x / log x < θ x - x)
    (x : ℝ) (hx0 : 0 < x) (hx22 : 22 ≤ log x) (_hx300 : log x < 300) :
    |θ x - x| < (1 / 1000) * x / log x := by
  by_cases h27 : log x < 27
  · exact dusart_initial_of_signed hx0 hx22 h27
      (hupper x hx0 hx22 h27) (hlower x hx0 hx22 h27)
  · exact dusart_tail_of_k2 hD x hx0 (le_of_not_gt h27)

end LeanLab.RieselVaughan1983.Task426
