import LeanLab.LZCesaroShort.Lemma3Coefficients

/-!
# The lower order coefficient moment in P0058 Lemma 3

AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1606.00869v2, page 3, Lemma 3, and the coefficient decomposition.
Chebyshev's bound suffices for the first moment. No PNT or RH input is needed.
-/

namespace LeanLab.LZCesaroShort

open Finset
open scoped ArithmeticFunction.vonMangoldt Chebyshev

/-- Chebyshev's bound gives a linear bound for the weighted first Lambda moment. -/
theorem lambda_first_moment_le {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, Λ n * Real.exp (-2 * n / N)) ≤ (Real.log 4 + 4) * N / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let q := Real.exp (-2 / (N : ℝ))
  let C : ℝ := Real.log 4 + 4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by norm_num) hN0
  have hqn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have hd : 0 < 1 - q := by linarith
  have he : ∀ n : ℕ, Real.exp (-2 * n / N) = q ^ n := by
    intro n
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hf : Summable (fun n : ℕ => Λ n * q ^ n) :=
    (summable_lambda_exp_two hN).congr (fun n => by rw [he n])
  have hg : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hfn : Summable (fun n : ℕ => ‖Λ n * q ^ n‖) := by
    refine hf.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (pow_nonneg hq0 n))]
  have hgn : Summable (fun n : ℕ => ‖q ^ n‖) := by
    refine hg.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 n)]
  have hconv : ∀ m : ℕ,
      (∑ k ∈ range (m + 1), (Λ k * q ^ k) * q ^ (m - k)) = ψ (m : ℝ) * q ^ m := by
    intro m
    rw [← sum_range_vonMangoldt m, sum_mul]
    apply sum_congr rfl
    intro k hk
    rw [mul_assoc, ← pow_add, show k + (m - k) = m by have := mem_range.mp hk; omega]
  have hprod0 := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfn hgn
  simp_rw [hconv] at hprod0
  have hprod : (∑' n : ℕ, Λ n * q ^ n) * (1 / (1 - q)) =
      ∑' n : ℕ, ψ (n : ℝ) * q ^ n := by
    calc
      _ = (∑' n : ℕ, Λ n * q ^ n) * (∑' n : ℕ, q ^ n) := by
        rw [tsum_geometric_of_lt_one hq0 hq1, one_div]
      _ = _ := hprod0
  have hnq := (hasSum_coe_mul_geometric_of_norm_lt_one hqn).summable
  have hpoint : ∀ m : ℕ, ψ (m : ℝ) * q ^ m ≤ C * ((m : ℝ) * q ^ m) := by
    intro m
    have hp := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) m)
    calc
      _ ≤ (C * m) * q ^ m := mul_le_mul_of_nonneg_right hp (pow_nonneg hq0 m)
      _ = _ := by ring
  have hps : Summable (fun n : ℕ => ψ (n : ℝ) * q ^ n) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Chebyshev.psi_nonneg _) (pow_nonneg hq0 n)) hpoint
      (hnq.mul_left C)
  have hsum : (∑' n : ℕ, ψ (n : ℝ) * q ^ n) ≤ C * q / (1 - q) ^ 2 := by
    calc
      _ ≤ ∑' n : ℕ, C * ((n : ℝ) * q ^ n) := hps.tsum_le_tsum hpoint (hnq.mul_left C)
      _ = C * (q / (1 - q) ^ 2) := by
        rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hqn]
      _ = _ := by ring
  have hF : (∑' n : ℕ, Λ n * q ^ n) ≤ C * q / (1 - q) := by
    have hm := mul_le_mul_of_nonneg_right hsum hd.le
    rw [← hprod] at hm
    have hl : (∑' n : ℕ, Λ n * q ^ n) * (1 / (1 - q)) * (1 - q) =
        (∑' n : ℕ, Λ n * q ^ n) := by field_simp [hd.ne']
    have hr : C * q / (1 - q) ^ 2 * (1 - q) = C * q / (1 - q) := by
      field_simp [hd.ne']
    rwa [hl, hr] at hm
  have hqx : q * Real.exp (2 / (N : ℝ)) = 1 := by
    dsimp [q]
    rw [← Real.exp_add, show -2 / (N : ℝ) + 2 / N = 0 by ring, Real.exp_zero]
  have hgeo : q / (1 - q) ≤ (N : ℝ) / 2 := by
    have hexp : 1 + 2 / (N : ℝ) ≤ Real.exp (2 / (N : ℝ)) := by
      linarith [Real.add_one_le_exp (2 / (N : ℝ))]
    have hm := mul_le_mul_of_nonneg_left hexp hq0
    rw [hqx] at hm
    have hs := mul_le_mul_of_nonneg_right hm (by positivity : (0 : ℝ) ≤ N / 2)
    have halg : q * (1 + 2 / (N : ℝ)) * (N / 2) = q * N / 2 + q := by
      field_simp
    rw [halg] at hs
    rw [div_le_iff₀ hd]
    nlinarith
  calc
    (∑' n : ℕ, Λ n * Real.exp (-2 * n / N)) = ∑' n : ℕ, Λ n * q ^ n := by
      apply tsum_congr
      intro n
      rw [he n]
    _ ≤ C * q / (1 - q) := hF
    _ = C * (q / (1 - q)) := by ring
    _ ≤ C * (N / 2) := mul_le_mul_of_nonneg_left hgeo hC
    _ = (Real.log 4 + 4) * N / 2 := by dsimp [C]; ring

end LeanLab.LZCesaroShort
