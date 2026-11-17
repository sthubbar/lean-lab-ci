import LeanLab.RieselVaughan1983.Lemma6Theta
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
Supply for U-1674 and the initial lower theta leaf in DecompJ246.
The split follows Rosser and Schoenfeld 1975 pages 265 to 267.
The cited estimates and the finite initial interval remain explicit leaves.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Chebyshev Set

namespace LeanLab.RieselVaughan1983.Task600

/-- Auxiliary endpoint arithmetic for the use of RS1962 page 72 display 4.6. -/
theorem initial_log_upper : log (1263229 : ℝ) < 7024591 / 500000 := by
  apply (log_lt_iff_lt_exp (by norm_num)).mpr
  have hsmall := sum_le_exp_of_nonneg (x := (24591 / 500000 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hsmall
  have hone := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    exp_one_gt_d9.le 14
  have heq : exp (7024591 / 500000 : ℝ) = exp 1 ^ 14 * exp (24591 / 500000) := by
    rw [← exp_nat_mul, ← exp_add]
    norm_num
  rw [heq]
  have hprod := mul_le_mul hone hsmall (by positivity)
    (by positivity : (0 : ℝ) ≤ exp 1 ^ 14)
  norm_num at hprod ⊢
  linarith

/-- The square root exceeds eighty logarithms above the exact middle endpoint.
Auxiliary arithmetic for RS1975 page 266 display 5.7 using RS1962 display 4.6. -/
theorem sqrt_gt_eighty_log (x : ℝ) (hx : 1263229 ≤ x) :
    80 * log x < sqrt x := by
  have hx0 : 0 < x := by linarith
  have hbase : exp 2 ≤ (1263229 : ℝ) := by
    have he := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_d9.le 2
    rw [exp_one_pow] at he
    norm_num at he ⊢
    linarith
  have hmono := log_div_sqrt_antitoneOn hbase (hbase.trans hx) hx
  have hs : (11239346 / 10000 : ℝ) < sqrt 1263229 := by
    apply (lt_sqrt (by norm_num)).mpr
    norm_num
  have hlog := initial_log_upper
  have hbudget : log (1263229 : ℝ) / sqrt 1263229 < 1 / 80 := by
    apply (div_lt_iff₀ (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1263229))).mpr
    linarith
  have hquot := hmono.trans_lt hbudget
  have h := (div_lt_iff₀ (sqrt_pos.mpr hx0)).mp hquot
  linarith

/-- A uniform prime-power budget on the bounded large interval.
Auxiliary arithmetic for RS1962 page 73 display 4.12. -/
theorem initial_gap_budget (x : ℝ) (hx : 10 ^ 8 ≤ x) (hu : x < 908994923) :
    sqrt x + 3 * x ^ (1 / 3 : ℝ) ≤ (13 / 100000 : ℝ) * x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : (10000 : ℝ) ≤ sqrt x := by
    apply (le_sqrt (by norm_num) hx0).mpr
    norm_num at hx ⊢
    exact hx
  have hsx := sq_sqrt hx0
  have hroot : sqrt x ≤ x / 10000 := by
    nlinarith [mul_nonneg (sqrt_nonneg x) (sub_nonneg.mpr hs)]
  have hc : x ^ (1 / 3 : ℝ) ≤ 1000 := by
    calc
      x ^ (1 / 3 : ℝ) ≤ ((1000 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) :=
        rpow_le_rpow hx0 (by norm_num at hu ⊢; linarith) (by norm_num)
      _ = 1000 := by rw [← rpow_natCast_mul (by norm_num)]; norm_num
  norm_num at hx
  linarith

/-- The large initial interval lies in the logarithmic range of the selected rows.
Auxiliary endpoint checks for RS1975 page 267. -/
theorem initial_log_range (x : ℝ) (hx : 10 ^ 8 ≤ x) (hu : x < 908994923) :
    (921 / 50 : ℝ) ≤ log x ∧ log x < 21 := by
  have hx0 : 0 < x := by linarith
  constructor
  · apply (le_log_iff_exp_le hx0).mpr
    have h42 : exp (42 / 100 : ℝ) ≤ 1522 / 1000 := by
      have h := exp_bound' (x := (42 / 100 : ℝ)) (by norm_num) (by norm_num)
        (n := 6) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h
      linarith
    have hp := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_d9.le 18
    have heq : exp (921 / 50 : ℝ) = exp 1 ^ 18 * exp (42 / 100 : ℝ) := by
      rw [← exp_nat_mul, ← exp_add]
      norm_num
    rw [heq]
    have hmul := mul_le_mul hp h42 (exp_pos _).le (by positivity)
    exact hmul.trans ((by norm_num :
      (2.7182818286 : ℝ) ^ 18 * (1522 / 1000) ≤ 10 ^ 8).trans hx)
  · apply (log_lt_iff_lt_exp hx0).mpr
    have h := Lemma6Theta.exp_nat_ge 21
    norm_num at h
    linarith

/-- Each selected epsilon fits the budget after adding the uniform prime-power gap.
The triple records the lower and upper logarithmic endpoints and the printed epsilon. -/
theorem row_coefficient_budget (b u ε : ℝ)
    (hrow : (b, u, ε) ∈
      ([(18.42, 18.43, 0.0012015), (18.43, 18.44, 0.0011969),
        (18.44, 18.45, 0.0011924), (18.45, 18.5, 0.0011878),
        (18.5, 18.7, 0.0011653), (18.7, 19, 0.0010800),
        (19, 19.5, 0.00096459), (19.5, 20, 0.00080243),
        (20, 21, 0.00065941)] : List (ℝ × ℝ × ℝ))) :
    0 ≤ ε ∧ (ε + 13 / 100000) * u < 1 / 40 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrow
  rcases hrow with h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl, rfl⟩; norm_num

/-- The requested normalized error budget on any one selected band.
This is arithmetic only. No psi or theta source estimate is used. -/
theorem normalized_row_budget (x u ε : ℝ) (hx : 10 ^ 8 ≤ x)
    (hu : x < 908994923) (hL : log x ≤ u) (hε : 0 ≤ ε)
    (hbudget : (ε + 13 / 100000) * u < 1 / 40) :
    ε + x ^ (-1 / 2 : ℝ) + 3 * x ^ (-2 / 3 : ℝ) < 1 / (40 * log x) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < log x := log_pos (by linarith)
  have hgap := initial_gap_budget x hx hu
  have hhalf : x ^ (-1 / 2 : ℝ) * x = sqrt x := by
    calc
      _ = x ^ ((-1 / 2 : ℝ) + 1) := by rw [rpow_add hx0, rpow_one]
      _ = _ := by norm_num [sqrt_eq_rpow]
  have hthird : x ^ (-2 / 3 : ℝ) * x = x ^ (1 / 3 : ℝ) := by
    calc
      _ = x ^ ((-2 / 3 : ℝ) + 1) := by rw [rpow_add hx0, rpow_one]
      _ = _ := by norm_num
  have hid : (ε + x ^ (-1 / 2 : ℝ) + 3 * x ^ (-2 / 3 : ℝ)) * x =
      ε * x + sqrt x + 3 * x ^ (1 / 3 : ℝ) := by
    rw [add_mul, add_mul, mul_assoc, hhalf, hthird]
  have hnorm : ε + x ^ (-1 / 2 : ℝ) + 3 * x ^ (-2 / 3 : ℝ) ≤
      ε + 13 / 100000 := by
    apply (mul_le_mul_iff_left₀ hx0).mp
    nlinarith [hid]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 40 * log x)).mpr
  have hcoef := mul_le_mul_of_nonneg_left hL (show 0 ≤ ε + 13 / 100000 by linarith)
  have hscaled := mul_le_mul_of_nonneg_right hnorm hlog.le
  nlinarith

/-- LEAF. RS1975 page 267 table, epsilon column, from page 263 display 4.8.
Only the nine bounded bands needed for page 266 display 5.7 are requested.
CITED analytic input. Consumers are CONDITIONAL ON these psi rows. -/
theorem rs1975_psi_rows (b u ε x : ℝ)
    (hrow : (b, u, ε) ∈
      ([(18.42, 18.43, 0.0012015), (18.43, 18.44, 0.0011969),
        (18.44, 18.45, 0.0011924), (18.45, 18.5, 0.0011878),
        (18.5, 18.7, 0.0011653), (18.7, 19, 0.0010800),
        (19, 19.5, 0.00096459), (19.5, 20, 0.00080243),
        (20, 21, 0.00065941)] : List (ℝ × ℝ × ℝ)))
    (hx : 10 ^ 8 ≤ x) (hb : b ≤ log x) (hu : log x ≤ u) :
    |ψ x - x| < ε * x := by
  sorry

/-- LEAF. RS1962 page 73 Theorem 24 display 4.12, with its full printed domain.
CITED input. Consumers are CONDITIONAL ON this finite prime-power estimate. -/
theorem rs1962_psi_theta_gap (x : ℝ) (hx : 0 < x) (hu : x ≤ 10 ^ 16) :
    ψ x - θ x < sqrt x + 3 * x ^ (1 / 3 : ℝ) := by
  sorry

/-- LEAF. RS1962 page 72 Theorem 19 display 4.6, on its second printed interval.
CITED finite estimate. Consumers are CONDITIONAL ON this input. -/
theorem rs1962_theta_sqrt_lower (x : ℝ) (hx : 1423 ≤ x) (hu : x ≤ 10 ^ 8) :
    x - 2 * sqrt x < θ x := by
  sorry

/-- Pointwise transfer of the RS1962 page 72 display 4.6 lower estimate.
CONDITIONAL ON that explicit pointwise estimate. The scalar comparison is proved. -/
theorem theta_lower_of_sqrt (x : ℝ) (hx : 1263229 ≤ x)
    (hθ : x - 2 * sqrt x < θ x) :
    x - x / (40 * log x) < θ x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := log_pos (by linarith)
  have hs := sqrt_gt_eighty_log x hx
  have hsx := sq_sqrt hx0.le
  have hsmall : 2 * sqrt x < x / (40 * log x) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 40 * log x)).mpr
    have hp := mul_pos (sqrt_pos.mpr hx0) (sub_pos.mpr hs)
    nlinarith
  linarith

/-- The middle range of RS1975 page 266 display 5.7.
CONDITIONAL ON RS1962 page 72 display 4.6. -/
theorem theta_lower_middle (x : ℝ) (hx : 1263229 ≤ x) (hu : x < 10 ^ 8) :
    x - x / (40 * log x) < θ x := by
  exact theta_lower_of_sqrt x hx (rs1962_theta_sqrt_lower x (by linarith) hu.le)

/-- Pointwise transfer from a psi error and the RS1962 display 4.12 gap.
CONDITIONAL ON the two explicit pointwise source estimates. -/
theorem theta_lower_of_normalized_error (x ε : ℝ) (hx : 0 < x)
    (hbudget : ε + x ^ (-1 / 2 : ℝ) + 3 * x ^ (-2 / 3 : ℝ) <
      1 / (40 * log x))
    (hpsi : |ψ x - x| < ε * x)
    (hgap : ψ x - θ x < sqrt x + 3 * x ^ (1 / 3 : ℝ)) :
    x - x / (40 * log x) < θ x := by
  have hhalf : x ^ (-1 / 2 : ℝ) * x = sqrt x := by
    calc
      _ = x ^ ((-1 / 2 : ℝ) + 1) := by rw [rpow_add hx, rpow_one]
      _ = _ := by norm_num [sqrt_eq_rpow]
  have hthird : x ^ (-2 / 3 : ℝ) * x = x ^ (1 / 3 : ℝ) := by
    calc
      _ = x ^ ((-2 / 3 : ℝ) + 1) := by rw [rpow_add hx, rpow_one]
      _ = _ := by norm_num
  have hscaled := mul_lt_mul_of_pos_right hbudget hx
  rw [add_mul, add_mul, mul_assoc, hhalf, hthird] at hscaled
  have hlow := (abs_lt.mp hpsi).1
  have hid : 1 / (40 * log x) * x = x / (40 * log x) := by ring
  rw [hid] at hscaled
  linarith

/-- The large range of RS1975 page 266 display 5.7 from nine page 267 rows.
CONDITIONAL ON the psi table and RS1962 page 73 display 4.12.
Every band choice and normalized error budget is proved. -/
theorem theta_lower_large (x : ℝ) (hx : 10 ^ 8 ≤ x) (hu : x < 908994923) :
    x - x / (40 * log x) < θ x := by
  have hx0 : 0 < x := by linarith
  have hlogs := initial_log_range x hx hu
  have hgap := rs1962_psi_theta_gap x hx0 (by norm_num at hu ⊢; linarith)
  have row (b u ε : ℝ)
      (hrow : (b, u, ε) ∈
        ([(18.42, 18.43, 0.0012015), (18.43, 18.44, 0.0011969),
          (18.44, 18.45, 0.0011924), (18.45, 18.5, 0.0011878),
          (18.5, 18.7, 0.0011653), (18.7, 19, 0.0010800),
          (19, 19.5, 0.00096459), (19.5, 20, 0.00080243),
          (20, 21, 0.00065941)] : List (ℝ × ℝ × ℝ)))
      (hb : b ≤ log x) (hL : log x ≤ u) :
      x - x / (40 * log x) < θ x := by
    have hc := row_coefficient_budget b u ε hrow
    exact theta_lower_of_normalized_error x ε hx0
      (normalized_row_budget x u ε hx hu hL hc.1 hc.2)
      (rs1975_psi_rows b u ε x hrow hx hb hL) hgap
  by_cases h1843 : log x ≤ 18.43
  · exact row 18.42 18.43 0.0012015 (by simp) (by convert hlogs.1 using 1 <;> norm_num) h1843
  by_cases h1844 : log x ≤ 18.44
  · exact row 18.43 18.44 0.0011969 (by simp) (by linarith) h1844
  by_cases h1845 : log x ≤ 18.45
  · exact row 18.44 18.45 0.0011924 (by simp) (by linarith) h1845
  by_cases h185 : log x ≤ 18.5
  · exact row 18.45 18.5 0.0011878 (by simp) (by linarith) h185
  by_cases h187 : log x ≤ 18.7
  · exact row 18.5 18.7 0.0011653 (by simp) (by linarith) h187
  by_cases h19 : log x ≤ 19
  · exact row 18.7 19 0.0010800 (by simp) (by linarith) h19
  by_cases h195 : log x ≤ 19.5
  · exact row 19 19.5 0.00096459 (by simp) (by linarith) h195
  by_cases h20 : log x ≤ 20
  · exact row 19.5 20 0.00080243 (by simp) (by linarith) h20
  exact row 20 21 0.00065941 (by simp) (by linarith) hlogs.2.le

/-- LEAF. RS1975 page 266 display 5.7 on the remaining finite initial interval.
Its written proof uses the Appel and Rosser tables of 1961.
The finite theta computation has not been certified here. -/
theorem theta_lower_finite (x : ℝ) (hx : 678407 ≤ x) (hu : x < 1263229) :
    x - x / (40 * log x) < θ x := by
  sorry

/-- Three-range supply for the sealed Task202 initial theta statement.
CONDITIONAL ON the table rows, both RS1962 estimates and the finite initial leaf. -/
theorem rs1975_theta_lower_initial_supply (x : ℝ) (hx : 678407 ≤ x)
    (hxD : x < 908994923) :
    x - x / (40 * log x) < θ x := by
  by_cases hlarge : 10 ^ 8 ≤ x
  · exact theta_lower_large x hlarge hxD
  by_cases hmiddle : 1263229 ≤ x
  · exact theta_lower_middle x hmiddle (lt_of_not_ge hlarge)
  exact theta_lower_finite x hx (lt_of_not_ge hmiddle)

end LeanLab.RieselVaughan1983.Task600
