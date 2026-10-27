import Mathlib
import LeanLab.Routes.U1441Katai

namespace LeanLab.Routes.U9061

open Finset
open LeanLab.Routes.U1441

/-- The Turan-Kubilius norm for a general finite set S and prime set P:
`|| w - M ||^2 = Σ_{n ∈ S} (w(n) - M)^2`. -/
def turanKubiliusVar (S : Finset ℕ) (w : ℕ → ℝ) (M : ℝ) : ℝ :=
  ∑ n ∈ S, (w n - M) ^ 2

/-- The Katai inequality for functions bounded by 1, over a general finite domain. -/
theorem katai_bounded (S P : Finset ℕ) (g w : ℕ → ℝ)
    (hw : ∀ n ∈ S, w n = (P.filter (· ∣ n)).card)
    (hg : ∀ n ∈ S, |g n| ≤ 1) (M : ℝ) (hM : 0 < M) :
    (∑ n ∈ S, g n) ^ 2 ≤
      (2 / M ^ 2) * (∑ p ∈ P, |∑ n ∈ S.filter (p ∣ ·), g n|)^2 +
      (2 / M ^ 2) * (S.card : ℝ) * turanKubiliusVar S w M := by
  have h_split : M * ∑ n ∈ S, g n = ∑ n ∈ S, g n * w n - ∑ n ∈ S, g n * (w n - M) := by
    rw [← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    ring
  have h_w : ∑ n ∈ S, g n * w n = ∑ p ∈ P, ∑ n ∈ S.filter (p ∣ ·), g n := by
    have h_w_eq : ∑ n ∈ S, g n * w n = ∑ n ∈ S, g n * ((P.filter (· ∣ n)).card : ℝ) := by
      refine sum_congr rfl fun n hn => ?_
      rw [hw n hn]
    rw [h_w_eq, weight_swap]
  have h_w_abs : |∑ n ∈ S, g n * w n| ≤ ∑ p ∈ P, |∑ n ∈ S.filter (p ∣ ·), g n| := by
    rw [h_w]
    exact norm_sum_le P (fun p => ∑ n ∈ S.filter (p ∣ ·), g n)
  have h_w_sq : (∑ n ∈ S, g n * w n)^2 ≤ (∑ p ∈ P, |∑ n ∈ S.filter (p ∣ ·), g n|)^2 := by
    have h1 : 0 ≤ |∑ n ∈ S, g n * w n| := abs_nonneg _
    have h3 := mul_self_le_mul_self h1 h_w_abs
    have h4 : |∑ n ∈ S, g n * w n|^2 = (∑ n ∈ S, g n * w n)^2 := sq_abs _
    have h5 : |∑ n ∈ S, g n * w n| * |∑ n ∈ S, g n * w n| = |∑ n ∈ S, g n * w n|^2 := by ring
    have h6 : (∑ p ∈ P, |∑ n ∈ S.filter (p ∣ ·), g n|) * (∑ p ∈ P, |∑ n ∈ S.filter (p ∣ ·), g n|) = (∑ p ∈ P, |∑ n ∈ S.filter (p ∣ ·), g n|)^2 := by ring
    rw [← h4, ← h5, ← h6]
    exact h3
  have h_sq (A B : ℝ) : (A - B)^2 ≤ 2 * A^2 + 2 * B^2 := by
    have H : 0 ≤ (A + B)^2 := sq_nonneg _
    linarith
  have h_bound1 : (M * ∑ n ∈ S, g n)^2 ≤ 2 * (∑ p ∈ P, |∑ n ∈ S.filter (p ∣ ·), g n|)^2 + 2 * (∑ n ∈ S, g n * (w n - M))^2 := by
    have h_bound : (M * ∑ n ∈ S, g n)^2 ≤ 2 * (∑ n ∈ S, g n * w n)^2 + 2 * (∑ n ∈ S, g n * (w n - M))^2 := by
      rw [h_split]
      exact h_sq _ _
    linarith
  have h_cs1 : (∑ n ∈ S, g n * (w n - M))^2 ≤ (∑ n ∈ S, (g n)^2) * turanKubiliusVar S w M := by
    exact sum_mul_sq_le_sq_mul_sq S g (fun n => w n - M)
  have h_gsq : ∑ n ∈ S, (g n)^2 ≤ S.card := by
    have H1 : ∑ n ∈ S, (g n)^2 ≤ ∑ n ∈ S, (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hgn : |g n| ≤ 1 := hg n hn
      have hgn_sq : |g n|^2 ≤ 1^2 := by gcongr
      have hsq : (g n)^2 = |g n|^2 := by exact (sq_abs (g n)).symm
      rw [hsq]
      linarith
    rw [sum_const, nsmul_eq_mul, mul_one] at H1
    exact H1
  have h_cs2 : (∑ n ∈ S, g n * (w n - M))^2 ≤ S.card * turanKubiliusVar S w M := by
    have H2 : 0 ≤ turanKubiliusVar S w M := by
      apply sum_nonneg
      intro n _
      exact sq_nonneg _
    exact le_trans h_cs1 (mul_le_mul_of_nonneg_right h_gsq H2)
  have h_bound2 : (M * ∑ n ∈ S, g n)^2 ≤ 2 * (∑ p ∈ P, |∑ n ∈ S.filter (p ∣ ·), g n|)^2 + 2 * (S.card : ℝ) * turanKubiliusVar S w M := by
    linarith
  have h_div : (∑ n ∈ S, g n)^2 = (M * ∑ n ∈ S, g n)^2 / M^2 := by
    have h_mul : (M * ∑ n ∈ S, g n)^2 = M^2 * (∑ n ∈ S, g n)^2 := mul_pow M (∑ n ∈ S, g n) 2
    rw [h_mul, mul_div_cancel_left₀]
    exact pow_ne_zero 2 (ne_of_gt hM)
  rw [h_div]
  have h_div_le : (M * ∑ n ∈ S, g n)^2 / M^2 ≤ (2 * (∑ p ∈ P, |∑ n ∈ S.filter (p ∣ ·), g n|)^2 + 2 * (S.card : ℝ) * turanKubiliusVar S w M) / M^2 := by
    apply div_le_div_of_nonneg_right h_bound2
    exact sq_nonneg M
  have h_split_div : (2 * (∑ p ∈ P, |∑ n ∈ S.filter (p ∣ ·), g n|)^2 + 2 * (S.card : ℝ) * turanKubiliusVar S w M) / M^2 = (2 / M^2) * (∑ p ∈ P, |∑ n ∈ S.filter (p ∣ ·), g n|)^2 + (2 / M^2) * S.card * turanKubiliusVar S w M := by
    ring
  rw [← h_split_div]
  exact h_div_le

end LeanLab.Routes.U9061
