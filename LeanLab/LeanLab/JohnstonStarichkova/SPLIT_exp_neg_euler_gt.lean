/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3, page 3, the factor e^(-γ) in U_N.
SPLIT of exp_neg_euler_gt, ROUTE BURST S98 burst-20261122.
AI wrote this Lean code.
-/
import LeanLab.JohnstonStarichkova.SPLIT_sifted_count_lower_v3

namespace LeanLab.JohnstonStarichkova
open LeanLab.AlmostPrimes
open Real Filter Topology

/-
Numerics: γ = 0.5772156649..., so γ < 0.57722 with margin 4.3e-6.
Then e^0.57722 = 1.7810801 < 1/0.56145 = 1.7811025.
-/
/-- The Euler Maclaurin corrected sequence H_n - log n - 1/(2n) + 1/(12 n^2), whose
decrease to the Euler constant gives the upper bound used for P0019 v3 page 3. Helper
notation, not a new definition, standard, see Havil, Gamma, chapter on the Euler Maclaurin formula. -/
local notation "eulerEMSeq" => fun n : ℕ =>
  (harmonic n : ℝ) - Real.log n - 1 / (2 * n) + 1 / (12 * (n : ℝ) ^ 2)

lemma js_log_one_add_inv_ge {a : ℝ} (ha : 0 < a) :
    2 * (1 / (2 * a + 1)) + 2 * (1 / 3) * (1 / (2 * a + 1)) ^ 3 +
      2 * (1 / 5) * (1 / (2 * a + 1)) ^ 5 ≤ Real.log (1 + a⁻¹) := by
  have h := hasSum_log_one_add_inv ha
  have hle := sum_le_hasSum (Finset.range 3) (fun i _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
  norm_num at hle ⊢
  linarith

lemma eulerEMSeq_succ_le {n : ℕ} (hn : 1 ≤ n) : eulerEMSeq (n + 1) ≤ eulerEMSeq n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : Real.log ((n : ℝ) + 1) - Real.log n = Real.log (1 + (n : ℝ)⁻¹) := by
    rw [← Real.log_div (by positivity) hn0.ne']
    congr 1; field_simp
  have hL := js_log_one_add_inv_ge hn0
  beta_reduce
  rw [harmonic_succ]
  push_cast
  have key : 1 / ((n : ℝ) + 1) + 1 / (2 * n) - 1 / (2 * ((n : ℝ) + 1)) - 1 / (12 * (n : ℝ) ^ 2)
      + 1 / (12 * ((n : ℝ) + 1) ^ 2) ≤
      2 * (1 / (2 * n + 1)) + 2 * (1 / 3) * (1 / (2 * (n : ℝ) + 1)) ^ 3 +
      2 * (1 / 5) * (1 / (2 * (n : ℝ) + 1)) ^ 5 := by
    rw [← sub_nonneg]
    have e : 2 * (1 / (2 * (n:ℝ) + 1)) + 2 * (1 / 3) * (1 / (2 * (n : ℝ) + 1)) ^ 3 +
      2 * (1 / 5) * (1 / (2 * (n : ℝ) + 1)) ^ 5 - (1 / ((n : ℝ) + 1) + 1 / (2 * n) - 1 / (2 * ((n : ℝ) + 1)) - 1 / (12 * (n : ℝ) ^ 2)
      + 1 / (12 * ((n : ℝ) + 1) ^ 2)) = (64 * (n:ℝ) ^ 4 + 128 * (n:ℝ) ^ 3 + 94 * (n:ℝ) ^ 2 + 30 * n + 5) /
        (60 * (n:ℝ) ^ 2 * ((n:ℝ) + 1) ^ 2 * (2 * n + 1) ^ 5) := by
      field_simp
      ring
    rw [e]; positivity
  have hi : ((n : ℝ) + 1)⁻¹ = 1 / ((n : ℝ) + 1) := (one_div _).symm
  linarith [hlog]

lemma eulerEMSeq_tendsto : Tendsto eulerEMSeq atTop (𝓝 eulerMascheroniConstant) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * n)) atTop (𝓝 0) := by
    have := h0.const_mul (1 / 2 : ℝ)
    rw [mul_zero] at this
    refine this.congr (fun n => ?_); ring
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (12 * (n : ℝ) ^ 2)) atTop (𝓝 0) := by
    have := (h0.mul h0).const_mul (1 / 12 : ℝ)
    rw [mul_zero, mul_zero] at this
    refine this.congr (fun n => ?_); ring
  have := (tendsto_harmonic_sub_log.sub h1).add h2
  rw [sub_zero, add_zero] at this
  exact this.congr (fun n => rfl)

lemma gamma_le_eulerEMSeq_ten : eulerMascheroniConstant ≤ eulerEMSeq 10 := by
  let c : ℕ → ℝ := fun k => eulerEMSeq (k + 1)
  have hc : Antitone c := antitone_nat_of_succ_le (fun k => eulerEMSeq_succ_le (by omega))
  have ht : Tendsto c atTop (𝓝 eulerMascheroniConstant) :=
    eulerEMSeq_tendsto.comp (tendsto_add_atTop_nat 1)
  exact hc.le_of_tendsto ht 9

lemma js_log_ten_gt : (2.3025816 : ℝ) < Real.log 10 := by
  have h2 := Real.log_two_gt_d9
  have h54 := js_log_one_add_inv_ge (a := 4) (by norm_num)
  have e : Real.log 10 = 3 * Real.log 2 + Real.log (1 + (4 : ℝ)⁻¹) := by
    rw [← Real.log_rpow (by norm_num), ← Real.log_mul (by positivity) (by norm_num)]
    norm_num
  rw [e]; norm_num at h54; linarith

/-- P0019 v3 page 3 uses the Euler constant γ = 0.5772156649; the upper
bound γ < 0.57722 from H_n - log n - 1/(2n) + 1/(12n^2) decreasing to γ, at n = 10.
PROVED, burst S153, was the S98 LEAF. -/
theorem euler_lt_057722 : Real.eulerMascheroniConstant < (0.57722 : ℝ) := by
  refine lt_of_le_of_lt gamma_le_eulerEMSeq_ten ?_
  have hH : (harmonic 10 : ℝ) = 7381 / 2520 := by
    rw [show (7381 / 2520 : ℝ) = ((7381 / 2520 : ℚ) : ℝ) by push_cast; ring]
    congr 1
    norm_num [harmonic, Finset.sum_range_succ]
  have := js_log_ten_gt
  beta_reduce
  rw [hH]; push_cast
  norm_num
  linarith

/-- Exp step: e^0.57722 < 1/0.56145, by the degree 12 Taylor bound. -/
theorem exp_057722_lt : Real.exp (0.57722 : ℝ) < 1 / 0.56145 := by
  have h := Real.exp_bound' (x := (0.57722 : ℝ)) (by norm_num) (by norm_num) (n := 12)
    (by norm_num)
  refine lt_of_le_of_lt h ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

theorem exp_neg_euler_gt_split :
    (0.56145 : ℝ) < Real.exp (-Real.eulerMascheroniConstant) := by
  have h1 : Real.exp (-(0.57722 : ℝ)) < Real.exp (-Real.eulerMascheroniConstant) :=
    Real.exp_lt_exp.mpr (by linarith [euler_lt_057722])
  have h2 : (0.56145 : ℝ) < Real.exp (-(0.57722 : ℝ)) := by
    rw [Real.exp_neg]
    have hp := Real.exp_pos (0.57722 : ℝ)
    have h3 := exp_057722_lt
    rw [lt_inv_comm₀ (by norm_num) hp]
    calc Real.exp 0.57722 < 1 / 0.56145 := h3
      _ = (0.56145 : ℝ)⁻¹ := by norm_num
  linarith

end LeanLab.JohnstonStarichkova
