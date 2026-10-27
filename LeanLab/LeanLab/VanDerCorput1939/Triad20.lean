import Mathlib
import LeanLab.VanDerCorput1939.Global
import LeanLab.VanDerCorput1939.KBounds

namespace LeanLab.VanDerCorput1939.Triad20
open Real Finset

attribute [local instance] Classical.propDecidable

theorem aK_vals_48 : aK 0 = 0 ∧ aK 1 = 0 ∧ aK 2 = Real.log (2 / 1) ∧ aK 3 = Real.log (9 / 8) ∧ aK 4 = 0 ∧ aK 5 = Real.log (65 / 64) ∧ aK 6 = 0 ∧ aK 7 = Real.log (217 / 216) ∧
    aK 8 = 0 ∧ aK 9 = 0 ∧ aK 10 = 0 ∧ aK 11 = Real.log (1001 / 1000) ∧ aK 12 = 0 ∧ aK 13 = Real.log (1729 / 1728) ∧ aK 14 = 0 ∧ aK 15 = 0 ∧
    aK 16 = 0 ∧ aK 17 = Real.log (4097 / 4096) ∧ aK 18 = 0 ∧ aK 19 = Real.log (5833 / 5832) ∧ aK 20 = 0 ∧ aK 21 = 0 ∧ aK 22 = 0 ∧ aK 23 = Real.log (10649 / 10648) ∧
    aK 24 = 0 ∧ aK 25 = 0 ∧ aK 26 = 0 ∧ aK 27 = 0 ∧ aK 28 = 0 ∧ aK 29 = Real.log (21953 / 21952) ∧ aK 30 = 0 ∧ aK 31 = Real.log (27001 / 27000) ∧
    aK 32 = 0 ∧ aK 33 = 0 ∧ aK 34 = 0 ∧ aK 35 = 0 ∧ aK 36 = 0 ∧ aK 37 = Real.log (46657 / 46656) ∧ aK 38 = 0 ∧ aK 39 = 0 ∧
    aK 40 = 0 ∧ aK 41 = Real.log (64001 / 64000) ∧ aK 42 = 0 ∧ aK 43 = Real.log (74089 / 74088) ∧ aK 44 = 0 ∧ aK 45 = 0 ∧ aK 46 = 0 ∧ aK 47 = Real.log (97337 / 97336) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [aK, fK] <;> norm_num

/-- The head: primes below 48. -/
theorem head_eq : ∑ n ∈ range 48, aK n =
    Real.log 2 + Real.log (9 / 8) + Real.log (65 / 64) + Real.log (217 / 216) + Real.log (1001 / 1000) + Real.log (1729 / 1728) + Real.log (4097 / 4096) + Real.log (5833 / 5832) + Real.log (10649 / 10648) + Real.log (21953 / 21952) + Real.log (27001 / 27000) + Real.log (46657 / 46656) + Real.log (64001 / 64000) + Real.log (74089 / 74088) + Real.log (97337 / 97336) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47⟩ := aK_vals_48
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47]
  norm_num

/-- The tail by telescoping: `Σ_{n < N} 1/(n+47)² ≤ 1/46 − 1/(N+46)`. -/
theorem tail_sq_le (N : ℕ) : ∑ n ∈ range N, 1 / ((n : ℝ) + 47) ^ 2 ≤ 1 / 46 - 1 / ((N : ℝ) + 46) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have key : 1 / ((N : ℝ) + 47) ^ 2 ≤ 1 / ((N : ℝ) + 46) - 1 / ((N : ℝ) + 1 + 46) := by
      rw [show (N : ℝ) + 1 + 46 = N + 47 by ring]
      rw [div_sub_div _ _ (by positivity) (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem tail_le : ∑' n, aK (n + 48) ≤ 1 / 2162 := by
  have hterm : ∀ n : ℕ, aK (n + 48) ≤ 1 / 47 * (1 / ((n : ℝ) + 47) ^ 2) := by
    intro n
    have h := aK_le (n + 48)
    split_ifs at h with hp
    · refine h.trans ?_
      push_cast
      rw [show (n : ℝ) + 48 - 1 = n + 47 by ring]
      rw [div_le_iff₀ (by positivity)]
      rw [show 1 / 47 * (1 / ((n : ℝ) + 47) ^ 2) * ((n : ℝ) + 47) ^ 3 = ((n : ℝ) + 47) / 47 by
        field_simp]
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · exact h.trans (by positivity)
  apply Real.tsum_le_of_sum_range_le (fun n => aK_nonneg _)
  intro N
  calc ∑ n ∈ range N, aK (n + 48) ≤ ∑ n ∈ range N, 1 / 47 * (1 / ((n : ℝ) + 47) ^ 2) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = 1 / 47 * ∑ n ∈ range N, 1 / ((n : ℝ) + 47) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 1 / 47 * (1 / 46) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have := tail_sq_le N
        have : 0 ≤ 1 / ((N : ℝ) + 46) := by positivity
        linarith
    _ = 1 / 2162 := by norm_num

theorem log_head_eq : Real.log 2 + Real.log (9 / 8) + Real.log (65 / 64) + Real.log (217 / 216) + Real.log (1001 / 1000) + Real.log (1729 / 1728) + Real.log (4097 / 4096) + Real.log (5833 / 5832) + Real.log (10649 / 10648) + Real.log (21953 / 21952) + Real.log (27001 / 27000) + Real.log (46657 / 46656) + Real.log (64001 / 64000) + Real.log (74089 / 74088) + Real.log (97337 / 97336) =
    Real.log (2 * (9 / 8) * (65 / 64) * (217 / 216) * (1001 / 1000) * (1729 / 1728) * (4097 / 4096) * (5833 / 5832) * (10649 / 10648) * (21953 / 21952) * (27001 / 27000) * (46657 / 46656) * (64001 / 64000) * (74089 / 74088) * (97337 / 97336)) := by
  repeat rw [Real.log_mul (by norm_num) (by norm_num)]

/-- **Lower bound**: `2.300 < K`. -/
theorem K_gt : (2.300 : ℝ) < K := by
  rw [K_eq_exp]
  have hle : ∑ n ∈ range 48, aK n ≤ ∑' n, aK n :=
    summable_aK.sum_le_tsum _ (fun n _ => aK_nonneg n)
  rw [head_eq, log_head_eq] at hle
  have := Real.exp_le_exp.mpr hle
  rw [Real.exp_log (by norm_num)] at this
  have : (2.300 : ℝ) < 2 * (9 / 8) * (65 / 64) * (217 / 216) * (1001 / 1000) * (1729 / 1728) * (4097 / 4096) * (5833 / 5832) * (10649 / 10648) * (21953 / 21952) * (27001 / 27000) * (46657 / 46656) * (64001 / 64000) * (74089 / 74088) * (97337 / 97336) := by norm_num
  linarith

/-- **Upper bound**: `K < 2.302`. -/
theorem K_lt : K < (2.302 : ℝ) := by
  rw [K_eq_exp, ← summable_aK.sum_add_tsum_nat_add 48, head_eq, log_head_eq, Real.exp_add,
    Real.exp_log (by norm_num)]
  have ht := Real.exp_le_exp.mpr tail_le
  have hb : Real.exp (1 / 2162) ≤ 1 + 1 / 2162 + (1 / 2162) ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := 1 / 2162) (by norm_num [abs_of_pos])
    have := (abs_le.mp this).2
    linarith
  have hpos : (0 : ℝ) < 2 * (9 / 8) * (65 / 64) * (217 / 216) * (1001 / 1000) * (1729 / 1728) * (4097 / 4096) * (5833 / 5832) * (10649 / 10648) * (21953 / 21952) * (27001 / 27000) * (46657 / 46656) * (64001 / 64000) * (74089 / 74088) * (97337 / 97336) := by norm_num
  calc 2 * (9 / 8) * (65 / 64) * (217 / 216) * (1001 / 1000) * (1729 / 1728) * (4097 / 4096) * (5833 / 5832) * (10649 / 10648) * (21953 / 21952) * (27001 / 27000) * (46657 / 46656) * (64001 / 64000) * (74089 / 74088) * (97337 / 97336) * Real.exp (∑' n, aK (n + 48))
      ≤ 2 * (9 / 8) * (65 / 64) * (217 / 216) * (1001 / 1000) * (1729 / 1728) * (4097 / 4096) * (5833 / 5832) * (10649 / 10648) * (21953 / 21952) * (27001 / 27000) * (46657 / 46656) * (64001 / 64000) * (74089 / 74088) * (97337 / 97336) * (1 + 1 / 2162 + (1 / 2162) ^ 2) :=
        mul_le_mul_of_nonneg_left (ht.trans hb) hpos.le
    _ < 2.302 := by norm_num

theorem triad20_main : (2.300 : ℝ) < K ∧ K < 2.302 := ⟨K_gt, K_lt⟩

end LeanLab.VanDerCorput1939.Triad20
