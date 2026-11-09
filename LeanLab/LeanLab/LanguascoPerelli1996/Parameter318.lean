import LeanLab.LanguascoPerelli1996.Section5108

/-!
Derived real parameter estimates for P0071 page 360 display 25.
These elementary estimates compare adjacent damping parameters.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Parameter318
open Real ArithmeticFunction

/-- Page 360 display 25, derived square root coefficient bound for changing N. -/
theorem lambda_le_two_sqrt (n : ℕ) : Λ n ≤ 2 * Real.sqrt n := by
  by_cases hn : n = 0
  · simp [hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hn0)
  rw [Real.log_sqrt hn0.le] at hl
  exact vonMangoldt_le_log.trans (by linarith)

/-- Page 360 display 25, derived linear and quadratic geometric majorant. -/
theorem lambda_mul_le {K : ℝ} (hK : 0 < K) (n : ℕ) :
    (n : ℝ) * Λ n ≤ Real.sqrt K * n + (n : ℝ) ^ 2 / Real.sqrt K := by
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsq : 2 * Real.sqrt n * Real.sqrt K ≤ (n : ℝ) + K := by
    nlinarith [sq_nonneg (Real.sqrt n - Real.sqrt K), Real.sq_sqrt hn0, Real.sq_sqrt hK.le]
  have hl := mul_le_mul_of_nonneg_right (lambda_le_two_sqrt n) hs.le
  have hb : Λ n ≤ Real.sqrt K + (n : ℝ) / Real.sqrt K := by
    have he : (Real.sqrt K + (n : ℝ) / Real.sqrt K) * Real.sqrt K = K + n := by
      field_simp
      nlinarith [Real.sq_sqrt hK.le]
    apply (mul_le_mul_iff_left₀ hs).mp
    rw [he]
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hb hn0
  convert hh using 1 <;> ring

/-- Page 360 display 25, derived damping difference estimate. -/
theorem damping_difference_le {N K : ℝ} (hN : 0 < N) (hNK : N ≤ K) (n : ℕ) :
    0 ≤ Real.exp (-(n : ℝ) / K) - Real.exp (-(n : ℝ) / N) ∧
      Real.exp (-(n : ℝ) / K) - Real.exp (-(n : ℝ) / N) ≤
        (N⁻¹ - K⁻¹) * (n : ℝ) * Real.exp (-(n : ℝ) / K) := by
  have hK : 0 < K := hN.trans_le hNK
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hi : K⁻¹ ≤ N⁻¹ := inv_anti₀ hN hNK
  constructor
  · apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv, div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left hi hn0]
  · have he : Real.exp (-(n : ℝ) / N) =
        Real.exp (-(n : ℝ) / K) * Real.exp (-((N⁻¹ - K⁻¹) * n)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-((N⁻¹ - K⁻¹) * n)))
      (Real.exp_pos (-(n : ℝ) / K)).le
    nlinarith

/-- Page 360 display 25, derived geometric denominator bound for N at least one. -/
theorem geometric_denominator_bound {K : ℝ} (hK : 1 ≤ K) :
    (1 - Real.exp (-1 / K))⁻¹ ≤ 2 * K := by
  have hK0 : 0 < K := by linarith
  have hr : Real.exp (-1 / K) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by norm_num) hK0)
  have hre : Real.exp (-1 / K) ≤ K / (K + 1) := by
    rw [show -1 / K = -(1 / K) by ring, Real.exp_neg, inv_eq_one_div]
    apply (div_le_div_iff₀ (Real.exp_pos _) (by linarith : 0 < K + 1)).2
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (1 / K)) hK0.le
    have he : (1 / K + 1) * K = K + 1 := by field_simp; ring
    rw [he] at hh
    linarith
  have hp : 0 < 1 - Real.exp (-1 / K) := by linarith
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hp).2
  have hh := (le_div_iff₀ (by linarith : 0 < K + 1)).1 hre
  nlinarith [mul_nonneg (show 0 ≤ K - 1 by linarith) hp.le]

/-- Page 360 display 25, derived bounds for the two geometric moment sums. -/
theorem geometric_moments_bound {K : ℝ} (hK : 1 ≤ K) :
    (∑' n : ℕ, (n : ℝ) * Real.exp (-1 / K) ^ n) ≤ 4 * K ^ 2 ∧
      (∑' n : ℕ, (n : ℝ) ^ 2 * Real.exp (-1 / K) ^ n) ≤ 16 * K ^ 3 := by
  let r := Real.exp (-1 / K)
  have hK0 : 0 < K := by linarith
  have hr0 : 0 < r := Real.exp_pos _
  have hr : r < 1 := by
    change Real.exp (-1 / K) < 1
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by norm_num) hK0)
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr0]
  have hi := geometric_denominator_bound hK
  have hi0 : 0 ≤ (1 - r)⁻¹ := by positivity
  have h1 := pow_le_pow_left₀ hi0 hi 2
  have h2 := pow_le_pow_left₀ hi0 hi 3
  constructor
  · rw [tsum_coe_mul_geometric_of_norm_lt_one hrn, div_eq_mul_inv, ← inv_pow]
    calc r * (1 - r)⁻¹ ^ 2 ≤ 1 * (2 * K) ^ 2 := mul_le_mul hr.le h1 (by positivity) (by norm_num)
      _ = _ := by ring
  · rw [tsum_sq_mul_geometric_of_norm_lt_one hrn, div_eq_mul_inv, ← inv_pow]
    have hn : r * (1 + r) ≤ 2 := by nlinarith
    calc r * (1 + r) * (1 - r)⁻¹ ^ 3 ≤ 2 * (2 * K) ^ 3 :=
      mul_le_mul hn h2 (by positivity) (by norm_num)
      _ = _ := by ring

end LeanLab.LanguascoPerelli1996.Parameter318

#print axioms LeanLab.LanguascoPerelli1996.Parameter318.lambda_le_two_sqrt
#print axioms LeanLab.LanguascoPerelli1996.Parameter318.lambda_mul_le
#print axioms LeanLab.LanguascoPerelli1996.Parameter318.damping_difference_le
#print axioms LeanLab.LanguascoPerelli1996.Parameter318.geometric_denominator_bound
#print axioms LeanLab.LanguascoPerelli1996.Parameter318.geometric_moments_bound
