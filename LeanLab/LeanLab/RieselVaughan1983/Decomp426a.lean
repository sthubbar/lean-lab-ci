import LeanLab.RieselVaughan1983.DecompJ246

/-!
Supply for the Schoenfeld source leaf in DecompJ206.
The split follows Schoenfeld 1976 page 357, proof of Theorem 7 star.
The bounded table calculation and the analytic exponential estimate remain open.
The coefficient transfer is proved independently of both leaves.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Chebyshev

namespace LeanLab.RieselVaughan1983.Task426

/-- LEAF. Schoenfeld 1976 page 358, epsilon column at b = 18.42, 20, 35, 1000.
Each fixed relative psi error is requested only on its bounded logarithmic band.
The interval cover and all coefficient products are proved separately. -/
theorem schoenfeld_relative_rows (b u ε t : ℝ)
    (hrow : (b, u, ε) ∈
      ([(921 / 50, 20, 11976 / 10000000), (20, 35, 65759 / 100000000),
        (35, 1000, 18314 / 1000000000), (1000, 1950, 70481 / 10000000000)] :
        List (ℝ × ℝ × ℝ)))
    (ht : 0 < t) (hb : b ≤ log t) (hu : log t ≤ u) :
    |psi t - t| < ε * t := by
  sorry

/-- The logarithmic threshold for the first selected page 358 row. -/
theorem schoenfeld_log_threshold (t : ℝ) (ht : 10 ^ 8 ≤ t) :
    (921 / 50 : ℝ) ≤ log t := by
  have ht0 : 0 < t := by linarith
  apply (le_log_iff_exp_le ht0).mpr
  have h42 : exp (42 / 100 : ℝ) ≤ 1522 / 1000 := by
    have h := exp_bound' (x := (42 / 100 : ℝ)) (by norm_num) (by norm_num)
      (n := 6) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hp : exp (1 : ℝ) ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 := by
    gcongr
    exact exp_one_lt_d9.le
  have heq : exp (921 / 50 : ℝ) = exp 1 ^ 18 * exp (42 / 100 : ℝ) := by
    rw [← exp_nat_mul, ← exp_add]
    norm_num
  rw [heq]
  have hmul := mul_le_mul hp h42 (exp_pos _).le (by positivity)
  exact hmul.trans ((by norm_num :
    (2.7182818286 : ℝ) ^ 18 * (1522 / 1000) ≤ 10 ^ 8).trans ht)

/-- The bounded table range from the four relative rows on page 358.
CONDITIONAL ON those rows. All logarithmic coverage and coefficient checks are proved. -/
theorem schoenfeld_table_range (t : ℝ) (ht : 10 ^ 8 ≤ t) (hL : log t < 1950) :
    |psi t - t| ≤ t / (40 * log t) := by
  have ht0 : 0 < t := by linarith
  have hstart := schoenfeld_log_threshold t ht
  have hlog : 0 < log t := by linarith
  have convert_row (u ε : ℝ) (hu : log t ≤ u) (hε : 0 ≤ ε)
      (hbudget : ε * u ≤ 1 / 40) (herror : |psi t - t| < ε * t) :
      |psi t - t| ≤ t / (40 * log t) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 40 * log t)).mpr
    have hmul := mul_lt_mul_of_pos_right herror hlog
    have hcoef := (mul_le_mul_of_nonneg_left hu hε).trans hbudget
    have hscaled := mul_le_mul_of_nonneg_right hcoef ht0.le
    nlinarith
  by_cases h20 : log t ≤ 20
  · apply convert_row 20 (11976 / 10000000) h20 (by norm_num) (by norm_num)
    exact schoenfeld_relative_rows (921 / 50) 20 (11976 / 10000000) t (by simp) ht0 hstart h20
  by_cases h35 : log t ≤ 35
  · apply convert_row 35 (65759 / 100000000) h35 (by norm_num) (by norm_num)
    exact schoenfeld_relative_rows (20) 35 (65759 / 100000000) t (by simp) ht0 (by linarith) h35
  by_cases h1000 : log t ≤ 1000
  · apply convert_row 1000 (18314 / 1000000000) h1000 (by norm_num) (by norm_num)
    exact schoenfeld_relative_rows (35) 1000 (18314 / 1000000000) t (by simp) ht0 (by linarith) h1000
  apply convert_row 1950 (70481 / 10000000000) hL.le (by norm_num) (by norm_num)
  exact schoenfeld_relative_rows (1000) 1950 (70481 / 10000000000) t (by simp) ht0 (by linarith) hL.le

/-- LEAF. Schoenfeld 1976 page 342, Theorem 11, equations 7.1 and 7.2.
Restrict the explicit exponential estimate to the tail used on page 357.
The numerical comparison with 1 divided by 40 log t is not part of this leaf. -/
theorem schoenfeld_exponential_tail (t : ℝ) (ht : 0 < t) (hL : 1950 ≤ log t) :
    |psi t - t| < t * sqrt (8 / (17 * Real.pi)) *
      sqrt (sqrt (log t / (9645908801 / 1000000000 : ℝ))) *
      exp (-sqrt (log t / (9645908801 / 1000000000 : ℝ))) := by
  sorry

/-- Numerical tail budget for the page 342 exponential error.
This auxiliary calculation for the page 357 split uses no analytic source leaf. -/
theorem schoenfeld_exponential_budget (L : ℝ) (hL : 1950 ≤ L) :
    sqrt (8 / (17 * Real.pi)) *
      sqrt (sqrt (L / (9645908801 / 1000000000 : ℝ))) *
      exp (-sqrt (L / (9645908801 / 1000000000 : ℝ))) < 1 / (40 * L) := by
  have hL0 : 0 < L := by linarith
  let R : ℝ := 9645908801 / 1000000000
  let X : ℝ := sqrt (L / R)
  have hR : 0 < R := by norm_num [R]
  have hXsq : X ^ 2 = L / R := sq_sqrt (by positivity)
  have hLX : L = R * X ^ 2 := by rw [hXsq]; field_simp
  have hX : 14 ≤ X := by
    have hs : R * X ^ 2 = L := hLX.symm
    norm_num [R] at hs
    nlinarith [sqrt_nonneg (L / R)]
  have hX0 : 0 < X := by linarith
  have hc : sqrt (8 / (17 * Real.pi)) ≤ 1 := by
    apply (sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 17 * Real.pi)).mpr
    nlinarith [Real.two_le_pi]
  have hcoef : sqrt (8 / (17 * Real.pi)) * R ≤ 10 := by
    calc _ ≤ 1 * R := mul_le_mul_of_nonneg_right hc hR.le
      _ ≤ 10 := by norm_num [R]
  have hpow : (14 : ℝ) ^ (11 / 4 : ℝ) ≤ 2744 := by
    calc (14 : ℝ) ^ (11 / 4 : ℝ) ≤ (14 : ℝ) ^ (3 : ℝ) :=
      rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2744 := by norm_num
  have he : (1100000 : ℝ) ≤ exp 14 := by
    have h := Lemma6Theta.exp_nat_ge 14
    norm_num at h
    linarith
  have hend : (14 : ℝ) ^ (11 / 4 : ℝ) * exp (-14) ≤ 2744 / 1100000 := by
    rw [exp_neg, ← div_eq_mul_inv]
    exact (div_le_div_of_nonneg_right hpow (exp_pos _).le).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) he)
  have hpower_majorant : X ^ (5 / 2 : ℝ) ≤ X ^ (11 / 4 : ℝ) :=
    rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hdecay := (mul_le_mul_of_nonneg_right hpower_majorant (exp_pos (-X)).le).trans
    ((Task202.rs1975_decay_le 14 X (by norm_num) hX).trans hend)
  have hratio : sqrt (8 / (17 * Real.pi)) * R * (X ^ (5 / 2 : ℝ) * exp (-X)) <
      1 / 40 := by
    calc _ ≤ 10 * (X ^ (5 / 2 : ℝ) * exp (-X)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ 10 * (2744 / 1100000) := mul_le_mul_of_nonneg_left hdecay (by norm_num)
      _ < _ := by norm_num
  have hpower : X ^ 2 * sqrt X = X ^ (5 / 2 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_natCast X 2, ← rpow_add hX0]
    norm_num
  have hid : (sqrt (8 / (17 * Real.pi)) * sqrt X * exp (-X)) * L =
      sqrt (8 / (17 * Real.pi)) * R * (X ^ (5 / 2 : ℝ) * exp (-X)) := by
    rw [hLX, ← hpower]
    ring
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 40 * L)).mpr
  change (sqrt (8 / (17 * Real.pi)) * sqrt X * exp (-X)) * (40 * L) < 1
  nlinarith [hid]

/-- Transfer of the page 342 analytic estimate through the proved numerical budget.
CONDITIONAL ON the displayed pointwise exponential estimate. -/
theorem schoenfeld_tail_transfer (t : ℝ) (ht : 0 < t) (hL : 1950 ≤ log t)
    (hE : |psi t - t| < t * sqrt (8 / (17 * Real.pi)) *
      sqrt (sqrt (log t / (9645908801 / 1000000000 : ℝ))) *
      exp (-sqrt (log t / (9645908801 / 1000000000 : ℝ)))) :
    |psi t - t| ≤ t / (40 * log t) := by
  have hb := mul_lt_mul_of_pos_left (schoenfeld_exponential_budget (log t) hL) ht
  have heq : t * (1 / (40 * log t)) = t / (40 * log t) := by ring
  rw [heq] at hb
  exact (hE.trans (by nlinarith [hb])).le

/-- Exact supply statement for Task246.schoenfeld_psi_error_large_leaf.
CONDITIONAL ON the bounded table range and the analytic exponential tail above.
The sealed source file is not changed. -/
theorem schoenfeld_psi_error_large_supply (t : ℝ) (ht : 10 ^ 8 ≤ t) :
    |psi t - t| ≤ t / (40 * log t) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 < t := by linarith
  have hlog : 0 < log t := log_pos ht1
  by_cases hL : 1950 ≤ log t
  · exact schoenfeld_tail_transfer t ht0 hL (schoenfeld_exponential_tail t ht0 hL)
  · exact schoenfeld_table_range t ht (lt_of_not_ge hL)

end LeanLab.RieselVaughan1983.Task426
