import LeanLab.LZCesaroShort.Theorem2bShort
import LeanLab.PNTPort.ExplicitPsi1.VonKoch2

/-!
# Sums of two prime powers in short windows, from RH alone

Lab proof, unit U-6107, CLOUD 20261020T0618Z-cloud36. AI wrote this file. CONDITIONAL ON
RiemannHypothesis only, through `theorem2b_short` and the lab's `vonKoch_RH_log2`.
Binary Goldbach is OPEN; this is about sums of two prime POWERS, on average over a window.

* `weighted_R_pos_short`: under RH there are `C` and `N₀` with
  `Σ_{|n − N| ≤ H} e^{−n/N} (1 − |n − N|/H) R(n) > 0` for every `N ≥ N₀` and every `H` with
  `C log² N ≤ H` and `2H(log N + 1) ≤ √N`;
* `exists_R_pos_short_RH`: hence every such window `[N − H, N + H]` holds a sum of two prime powers.

KNOWN in substance: under RH every interval of length `C log² N` holds a sum of two primes,
Linnik 1952 and later Kaczorowski, Perelli and Pintz; the explicit RH forms are I-0010 and
I-5001 to I-5011 in the lab, through Chirre-Hagen's cited bound. What is new here is only that
the chain from RH to the window statement now runs through the lab's own Selberg mean square
with no cited input.
-/

namespace LeanLab.LZCesaroShort

open Finset Filter
open scoped ArithmeticFunction.vonMangoldt Chebyshev

lemma exp_neg_two_ge : (1 : ℝ) / 8 ≤ Real.exp (-2) := by
  rw [Real.exp_neg, one_div]
  apply inv_anti₀ (Real.exp_pos 2)
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e]; nlinarith [Real.exp_pos 1]

set_option maxHeartbeats 4000000 in
/-- **Positivity of the weighted count, under RH.** -/
theorem weighted_R_pos_short (hRH : RiemannHypothesis) : ∃ C : ℝ, ∃ N₀ : ℕ,
    ∀ N H : ℕ, N₀ ≤ N → C * Real.log N ^ 2 ≤ H → 2 * H * (Real.log N + 1) ≤ Real.sqrt N →
      0 < ∑ n ∈ Icc (N - H) (N + H), Real.exp (-(n : ℝ) / N) * w N H n * R n := by
  obtain ⟨K, hK, hT2⟩ := theorem2b_short hRH
  obtain ⟨Cv, hCv⟩ := LeanLab.PNTPort.ExplicitPsi1.vonKoch_RH_log2 hRH
  set C' := |Cv|
  obtain ⟨Ne, hNe⟩ := eventually_atTop.mp (eventually_small (128 * C'))
  refine ⟨64 * K + 1, max Ne (10 ^ 20), fun N H hN hCH hHs => ?_⟩
  have hNe' : Ne ≤ N := le_trans (le_max_left _ _) hN
  have hN20 : (10 : ℝ) ^ 20 ≤ N := by
    have : (10 ^ 20 : ℕ) ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast this
  have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hN20
  have hN0 : (0 : ℝ) < N := by linarith
  have hN16 : (16 : ℝ) ≤ N := le_trans (by norm_num) hN20
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hL2 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9; linarith
  have hH1 : (1 : ℝ) ≤ H := by
    have : (1 : ℝ) * 1 ≤ (64 * K + 1) * Real.log N ^ 2 :=
      mul_le_mul (by linarith) (by nlinarith) (by norm_num) (by linarith)
    linarith
  have hH : 1 ≤ H := by exact_mod_cast hH1
  have hH0 : (0 : ℝ) < H := by linarith
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hs4 : 4 ≤ Real.sqrt (N : ℝ) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hN16
  have hHsN : (H : ℝ) ≤ Real.sqrt N / 4 := by nlinarith
  have hHN2 : (H : ℝ) ≤ N / 4 := by nlinarith
  have hHN : H ≤ N := by exact_mod_cast (show (H : ℝ) ≤ N by linarith)
  -- Theorem 2 eq. (3)
  have hw2 := hT2 N H hN20 hH hHs
  have hlog2N : Real.log (2 * N / H) ≤ 2 * Real.log N := by
    have : 2 * (N : ℝ) / H ≤ (N : ℝ) ^ 2 := by rw [div_le_iff₀ hH0]; nlinarith
    calc _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlog2N0 : 0 ≤ Real.log (2 * N / H) := Real.log_nonneg (by rw [le_div_iff₀ hH0]; linarith)
  have hwb : |wsum N H H| ≤ H * N / 16 := by
    have h1 : Real.log (2 * N / H) ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
    have h2 : K * N * Real.log (2 * N / H) ^ 2 ≤ 4 * K * N * Real.log N ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ K * N by positivity); linarith
    have h3 : 64 * K * Real.log N ^ 2 ≤ H := by nlinarith [pow_nonneg hlogN.le 2]
    have h4 : 4 * K * N * Real.log N ^ 2 ≤ H * N / 16 := by nlinarith
    linarith
  -- the ψ term
  obtain ⟨_, hsm⟩ := hNe N hNe'
  have hB : ∀ n ∈ Icc (N - H) (N + H), |ψ (n : ℝ) - n| ≤ N / 64 := by
    intro n hn
    rw [mem_Icc] at hn
    have hn1 : (N : ℝ) - H ≤ n := by
      have : ((N - H : ℕ) : ℝ) ≤ n := by exact_mod_cast hn.1
      push_cast [Nat.cast_sub hHN] at this; linarith
    have hn2 : (n : ℝ) ≤ N + H := by exact_mod_cast hn.2
    have hn6 : (6 : ℝ) ≤ n := by nlinarith
    have hv := hCv n hn6
    have hn0 : (0 : ℝ) < n := by linarith
    have hs1 : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt N := by
      have : Real.sqrt (n : ℝ) ≤ Real.sqrt (4 * N) := Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    have hl1 : Real.log n ≤ 2 * Real.log N := by
      have : (n : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      calc _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log hn0 this
        _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
    have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hlsq : Real.log n ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
    have hCabs : Cv ≤ C' := le_abs_self Cv
    have hpsi : Cv * Real.sqrt n * Real.log n ^ 2 ≤ C' * (2 * Real.sqrt N) * (4 * Real.log N ^ 2) := by
      have hC0 : 0 ≤ C' := abs_nonneg Cv
      calc Cv * Real.sqrt n * Real.log n ^ 2 ≤ C' * Real.sqrt n * Real.log n ^ 2 := by
            have : 0 ≤ Real.sqrt n * Real.log n ^ 2 := by positivity
            nlinarith
        _ ≤ C' * (2 * Real.sqrt N) * (4 * Real.log N ^ 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hs1 hC0) hlsq (by positivity) (by positivity)
    have hsm' : 512 * C' * Real.log N ^ 2 ≤ Real.sqrt N := by nlinarith
    have : C' * (2 * Real.sqrt N) * (4 * Real.log N ^ 2) ≤ N / 64 := by
      have e : C' * (2 * Real.sqrt N) * (4 * Real.log N ^ 2) = (8 * C' * Real.log N ^ 2) * Real.sqrt N := by ring
      rw [e]
      have : 8 * C' * Real.log N ^ 2 ≤ Real.sqrt N / 64 := by linarith
      have := mul_le_mul_of_nonneg_right this hsN.le
      nlinarith
    linarith
  -- the decomposition
  have hfilt : (Icc (N - H) (N + H)).filter (fun n : ℕ => (n : ℝ) ≤ N + H) = Icc (N - H) (N + H) := by
    apply filter_true_of_mem; intro n hn; rw [mem_Icc] at hn; exact_mod_cast hn.2
  have hdec : ∑ n ∈ Icc (N - H) (N + H), Real.exp (-(n : ℝ) / N) * w N H n * R n
      = wsum N H H + ∑ n ∈ Icc (N - H) (N + H), Real.exp (-(n : ℝ) / N) * w N H n * n
        + 2 * ∑ n ∈ Icc (N - H) (N + H), Real.exp (-(n : ℝ) / N) * w N H n * (ψ (n : ℝ) - n) := by
    unfold wsum; rw [hfilt, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    ring
  -- main term
  have hmain : (H : ℝ) * N / 8 ≤ ∑ n ∈ Icc (N - H) (N + H), Real.exp (-(n : ℝ) / N) * w N H n * n := by
    have hsw := sum_w_mul_n hH hHN
    have : ∑ n ∈ Icc (N - H) (N + H), (1 / 8 : ℝ) * (w N H n * n)
        ≤ ∑ n ∈ Icc (N - H) (N + H), Real.exp (-(n : ℝ) / N) * w N H n * n := by
      refine sum_le_sum fun n hn => ?_
      have hw0 := (w_mem hH (mem_Icc.mp hn).1 (mem_Icc.mp hn).2 hHN).1
      have hn2 : (n : ℝ) ≤ 2 * N := by
        have : (n : ℝ) ≤ N + H := by exact_mod_cast (mem_Icc.mp hn).2
        linarith
      have he : (1 / 8 : ℝ) ≤ Real.exp (-(n : ℝ) / N) := by
        refine exp_neg_two_ge.trans (Real.exp_le_exp.mpr ?_)
        rw [neg_div, neg_le_neg_iff, div_le_iff₀ hN0]; linarith
      have : 0 ≤ w N H n * n := mul_nonneg hw0 (Nat.cast_nonneg n)
      nlinarith
    rw [← mul_sum, hsw] at this
    linarith
  -- ψ term
  have hpsi : |∑ n ∈ Icc (N - H) (N + H), Real.exp (-(n : ℝ) / N) * w N H n * (ψ (n : ℝ) - n)|
      ≤ H * N / 64 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have : ∑ n ∈ Icc (N - H) (N + H), |Real.exp (-(n : ℝ) / N) * w N H n * (ψ (n : ℝ) - n)|
        ≤ ∑ n ∈ Icc (N - H) (N + H), w N H n * (N / 64) := by
      refine sum_le_sum fun n hn => ?_
      have hw := w_mem hH (mem_Icc.mp hn).1 (mem_Icc.mp hn).2 hHN
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hw.1]
      have he : Real.exp (-(n : ℝ) / N) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_div, neg_nonpos]; positivity
      have := hB n hn
      have h0 : 0 ≤ |ψ (n : ℝ) - n| := abs_nonneg _
      calc Real.exp (-(n : ℝ) / N) * w N H n * |ψ (n : ℝ) - n| ≤ 1 * w N H n * |ψ (n : ℝ) - n| := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hw.1) h0
        _ ≤ w N H n * (N / 64) := by rw [one_mul]; exact mul_le_mul_of_nonneg_left this hw.1
    rw [← sum_mul, sum_w hH hHN] at this
    linarith
  rw [hdec]
  have h1 := neg_abs_le (wsum N H H)
  have h2 := neg_abs_le (∑ n ∈ Icc (N - H) (N + H), Real.exp (-(n : ℝ) / N) * w N H n * (ψ (n : ℝ) - n))
  have : 0 < (H : ℝ) * N := by positivity
  nlinarith

/-- **Sums of two prime powers in every short window, under RH.** -/
theorem exists_R_pos_short_RH (hRH : RiemannHypothesis) : ∃ C : ℝ, ∃ N₀ : ℕ,
    ∀ N H : ℕ, N₀ ≤ N → C * Real.log N ^ 2 ≤ H → 2 * H * (Real.log N + 1) ≤ Real.sqrt N →
      ∃ n ∈ Icc (N - H) (N + H), ∃ a b : ℕ, IsPrimePow a ∧ IsPrimePow b ∧ a + b = n := by
  obtain ⟨C, N₀, h⟩ := weighted_R_pos_short hRH
  refine ⟨C, N₀, fun N H hN hC hHs => ?_⟩
  have hpos := h N H hN hC hHs
  by_contra hc
  push Not at hc
  have : ∑ n ∈ Icc (N - H) (N + H), Real.exp (-(n : ℝ) / N) * w N H n * R n = 0 := by
    refine sum_eq_zero fun n hn => ?_
    have hR : R n = 0 := by
      rcases (R_nonneg n).lt_or_eq with hlt | heq
      · obtain ⟨a, b, ha, hb, hab⟩ := primePow_sum_of_R_pos hlt
        exact absurd hab (hc n hn a b ha hb)
      · exact heq.symm
    rw [hR, mul_zero]
  linarith

end LeanLab.LZCesaroShort
