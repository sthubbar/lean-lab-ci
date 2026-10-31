/-
P0022, page 362 and the weighted square comparison on page 367.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Kaniecki1995.Decomp95

namespace LeanLab.Kaniecki1995.Weights95
open Real Complex Finset
open scoped ArithmeticFunction.vonMangoldt

/-- Page 362. On its stated support the tapered weight lies between zero and Lambda. -/
theorem weight_bounds {x a : ℝ} (hx : 1 < x) (ha : 1 < a) (n : ℕ)
    (hn : (n : ℝ) ≤ x ^ a) : 0 ≤ LamXA x a n ∧ LamXA x a n ≤ Λ n := by
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  unfold LamXA
  split_ifs with hnx
  · exact ⟨hΛ, le_rfl⟩
  have hx0 : 0 < x := by linarith
  have hxn : x < (n : ℝ) := lt_of_not_ge hnx
  have hn0 : 0 < (n : ℝ) := lt_trans hx0 hxn
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hd : 0 < (a - 1) * Real.log x := by positivity
  have hlo : 0 ≤ Real.log (x ^ a / n) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hn0).mpr (by simpa using hn)
  have hhi : Real.log (x ^ a / n) ≤ (a - 1) * Real.log x := by
    rw [Real.log_div (Real.rpow_pos_of_pos hx0 a).ne' hn0.ne', Real.log_rpow hx0]
    have hlogn := Real.log_le_log hx0 hxn.le
    nlinarith
  constructor
  · positivity
  · rw [div_le_iff₀ hd]
    exact mul_le_mul_of_nonneg_left hhi hΛ

/-- Page 367. The tapered square is bounded by Lambda times log n. -/
theorem weight_sq_le {x a : ℝ} (hx : 1 < x) (ha : 1 < a) (n : ℕ)
    (hn : (n : ℝ) ≤ x ^ a) : LamXA x a n ^ 2 ≤ Λ n * Real.log n := by
  obtain ⟨h0, h1⟩ := weight_bounds hx ha n hn
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hlog : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  nlinarith

/-- Page 363, display 4. The finite polynomial is bounded by the positive Lambda sum. -/
theorem polynomial_norm_le {x a c t : ℝ} (hx : 1 < x) (ha : 1 < a) :
    ‖Decomp95.polynomial x a c t‖ ≤
      ∑ n ∈ (range ⌈x ^ a⌉₊).filter (fun n : ℕ => 0 < n ∧ (n : ℝ) < x ^ a),
        Λ n / (n : ℝ) ^ Decomp95.sigma x c := by
  unfold Decomp95.polynomial
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  simp only [mem_filter] at hn
  obtain ⟨hn0, hnx⟩ := hn.2
  obtain ⟨hw0, hw⟩ := weight_bounds hx ha n hnx.le
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hw0,
    norm_natCast_cpow_of_pos hn0]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, zero_mul,
    sub_zero, add_zero]
  exact div_le_div_of_nonneg_right hw (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Page 362. The weight hypotheses hold for x equal to two, a equal to two and n equal to three. -/
theorem weight_instance :
    0 ≤ LamXA 2 2 3 ∧ LamXA 2 2 3 ≤ Λ 3 :=
  weight_bounds (by norm_num) (by norm_num) 3 (by norm_num)

end LeanLab.Kaniecki1995.Weights95

#print axioms LeanLab.Kaniecki1995.Weights95.weight_bounds
#print axioms LeanLab.Kaniecki1995.Weights95.weight_sq_le
#print axioms LeanLab.Kaniecki1995.Weights95.polynomial_norm_le
#print axioms LeanLab.Kaniecki1995.Weights95.weight_instance
