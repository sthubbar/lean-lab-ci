import LeanLab.RieselVaughan1983.Decomp600
import LeanLab.Common.PsiTheta.Bound

/-!
An alternative large-range route for U-1674.
The original RS1962 display 4.12 route stays in Decomp600.
The clean shared prime-power bound also fits the same row budgets.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Chebyshev

namespace LeanLab.RieselVaughan1983.Task600

/-- A clean scalar replacement budget for the large interval of RS1975 display 5.7.
The shared bound has coefficient 1.25 on sqrt x. -/
theorem sqrt_relative_budget (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    1.25 * sqrt x < (13 / 100000 : ℝ) * x := by
  have hx0 : 0 < x := by linarith
  have hs : (10000 : ℝ) ≤ sqrt x := by
    apply (le_sqrt (by norm_num) hx0.le).mpr
    norm_num at hx ⊢
    exact hx
  have hsx := sq_sqrt hx0.le
  have hp := mul_pos (sqrt_pos.mpr hx0)
    (show (0 : ℝ) < (13 / 100000) * sqrt x - 1.25 by linarith)
  nlinarith

/-- The uniform prime-power budget from the existing clean Costa Pereira route.
This auxiliary replacement for RS1962 display 4.12 has no cited input. -/
theorem psi_theta_uniform_gap (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    ψ x - θ x < (13 / 100000 : ℝ) * x := by
  exact (LeanLab.Common.PsiTheta.psi_sub_theta_lt_125 hx).trans
    (sqrt_relative_budget x hx)

/-- Cover the required logarithmic interval by the nine selected page 267 bands.
This is finite endpoint arithmetic with no analytic input. -/
theorem initial_band_cover (L : ℝ) (hl : 18.42 ≤ L) (hu : L < 21) :
    ∃ b u ε : ℝ, (b, u, ε) ∈
      ([(18.42, 18.43, 0.0012015), (18.43, 18.44, 0.0011969),
        (18.44, 18.45, 0.0011924), (18.45, 18.5, 0.0011878),
        (18.5, 18.7, 0.0011653), (18.7, 19, 0.0010800),
        (19, 19.5, 0.00096459), (19.5, 20, 0.00080243),
        (20, 21, 0.00065941)] : List (ℝ × ℝ × ℝ)) ∧ b ≤ L ∧ L ≤ u := by
  by_cases h1843 : L ≤ 18.43
  · exact ⟨18.42, 18.43, 0.0012015, by simp, hl, h1843⟩
  by_cases h1844 : L ≤ 18.44
  · exact ⟨18.43, 18.44, 0.0011969, by simp, by linarith, h1844⟩
  by_cases h1845 : L ≤ 18.45
  · exact ⟨18.44, 18.45, 0.0011924, by simp, by linarith, h1845⟩
  by_cases h185 : L ≤ 18.5
  · exact ⟨18.45, 18.5, 0.0011878, by simp, by linarith, h185⟩
  by_cases h187 : L ≤ 18.7
  · exact ⟨18.5, 18.7, 0.0011653, by simp, by linarith, h187⟩
  by_cases h19 : L ≤ 19
  · exact ⟨18.7, 19, 0.0010800, by simp, by linarith, h19⟩
  by_cases h195 : L ≤ 19.5
  · exact ⟨19, 19.5, 0.00096459, by simp, by linarith, h195⟩
  by_cases h20 : L ≤ 20
  · exact ⟨19.5, 20, 0.00080243, by simp, by linarith, h20⟩
  exact ⟨20, 21, 0.00065941, by simp, by linarith, hu.le⟩

/-- Pointwise relative psi error transfer with the clean uniform gap.
CONDITIONAL ON the explicit pointwise psi estimate only. -/
theorem theta_lower_of_uniform_gap (x u ε : ℝ) (hx : 10 ^ 8 ≤ x)
    (hL : log x ≤ u) (hε : 0 ≤ ε)
    (hbudget : (ε + 13 / 100000) * u < 1 / 40)
    (hpsi : |ψ x - x| < ε * x) :
    x - x / (40 * log x) < θ x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < log x := log_pos (by linarith)
  have hgap := psi_theta_uniform_gap x hx
  have hcoef : (ε + 13 / 100000) * log x < 1 / 40 :=
    (mul_le_mul_of_nonneg_left hL (by linarith)).trans_lt hbudget
  have hscalar : (ε + 13 / 100000) * x < x / (40 * log x) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 40 * log x)).mpr
    have hm := mul_lt_mul_of_pos_right hcoef hx0
    nlinarith
  have hlow := (abs_lt.mp hpsi).1
  linarith

/-- Alternative large interval of RS1975 display 5.7.
CONDITIONAL ON the psi rows only. It does not use the RS1962 gap leaf. -/
theorem theta_lower_large_clean_gap (x : ℝ) (hx : 10 ^ 8 ≤ x) (hu : x < 908994923) :
    x - x / (40 * log x) < θ x := by
  have hlogs := initial_log_range x hx hu
  obtain ⟨b, u, ε, hrow, hb, hL⟩ := initial_band_cover (log x)
    (by convert hlogs.1 using 1 <;> norm_num) hlogs.2
  have hc := row_coefficient_budget b u ε hrow
  exact theta_lower_of_uniform_gap x u ε hx hL hc.1 hc.2
    (rs1975_psi_rows b u ε x hrow hx hb hL)

/-- Alternative supply for the sealed initial theta statement.
CONDITIONAL ON the psi rows, RS1962 display 4.6 and the finite initial leaf.
The RS1962 display 4.12 input is absent from this alternative. -/
theorem rs1975_theta_lower_initial_clean_gap_supply (x : ℝ) (hx : 678407 ≤ x)
    (hxD : x < 908994923) :
    x - x / (40 * log x) < θ x := by
  by_cases hlarge : 10 ^ 8 ≤ x
  · exact theta_lower_large_clean_gap x hlarge hxD
  by_cases hmiddle : 1263229 ≤ x
  · exact theta_lower_middle x hmiddle (lt_of_not_ge hlarge)
  exact theta_lower_finite x hx (lt_of_not_ge hmiddle)

/-- The scalar RS1962 display 4.6 route fails at the preceding integer.
This is a bound on the scalar envelopes and makes no assertion of a paper error. -/
theorem middle_threshold_predecessor :
    sqrt (1263228 : ℝ) < 80 * log (1263228 : ℝ) := by
  have hlog : (8780738 / 625000 : ℝ) < log 1263228 := by
    apply (lt_log_iff_exp_lt (by norm_num)).mpr
    have hsmall := exp_bound' (x := (30738 / 625000 : ℝ)) (by norm_num)
      (by norm_num) (n := 7) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hsmall
    have hone := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_d9.le 14
    have heq : exp (8780738 / 625000 : ℝ) = exp 1 ^ 14 * exp (30738 / 625000) := by
      rw [← exp_nat_mul, ← exp_add]
      norm_num
    rw [heq]
    have hprod := mul_le_mul hone hsmall (exp_pos _).le (by positivity)
    norm_num at hprod ⊢
    linarith
  have hs : sqrt (1263228 : ℝ) < 5619671 / 5000 := by
    apply (sqrt_lt (by norm_num) (by norm_num)).mpr
    norm_num
  linarith

/-- The middle endpoint is the least integer at least eight for this scalar transfer.
Auxiliary threshold audit for the use of RS1962 page 72 display 4.6. -/
theorem middle_threshold_nat_iff (n : ℕ) (hn : 8 ≤ n) :
    80 * log (n : ℝ) < sqrt (n : ℝ) ↔ 1263229 ≤ n := by
  constructor
  · intro h
    by_contra hN
    have hnU : n ≤ 1263228 := by omega
    have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
    have hnUR : (n : ℝ) ≤ 1263228 := by exact_mod_cast hnU
    have hn0 : (0 : ℝ) < n := by linarith
    have he : exp (2 : ℝ) ≤ 8 := by
      have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_d9.le 2
      rw [exp_one_pow] at h
      norm_num at h ⊢
      linarith
    have hmono := log_div_sqrt_antitoneOn (he.trans hnR)
      (he.trans (by norm_num : (8 : ℝ) ≤ 1263228)) hnUR
    have hpre : (1 / 80 : ℝ) < log 1263228 / sqrt 1263228 := by
      apply (lt_div_iff₀ (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1263228))).mpr
      linarith [middle_threshold_predecessor]
    have hsmall : log (n : ℝ) / sqrt (n : ℝ) < 1 / 80 := by
      apply (div_lt_iff₀ (sqrt_pos.mpr hn0)).mpr
      linarith
    linarith
  · intro hN
    exact sqrt_gt_eighty_log n (by exact_mod_cast hN)

end LeanLab.RieselVaughan1983.Task600
