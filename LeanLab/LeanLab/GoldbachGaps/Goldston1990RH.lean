import LeanLab.LZCesaroShort.Theorem1PProved
import LeanLab.GoldbachGaps.Goldston1990Base

/-!
# Kátai, Montgomery-Vaughan and Linnik from RH alone, through P0058

Lab proof, unit U-6215, CLOUD 20261020T0817Z-cloud38, T1, P0030. AI wrote this file.
CONDITIONAL ON RiemannHypothesis only. Binary Goldbach is OPEN.

Goldston 1990 quotes, under RH, Kátai and Montgomery-Vaughan: every `[N, N + C log² N]` holds a
Goldbach number, and Linnik's weaker `log^{3+ε}` form. Goldston1990.lean cites both, and proves
them from Chirre-Hagen's cited Theorem 3. Here both follow from RH with no cited input:

* `cesaro_ge_of_printed`: the proof of `cesaro_pos_of_printed` gives `HN/8 ≤ cesaro N H`;
* `Rp`, `R_sub_Rp_le`, `Rp_odd_le`: pairs with a prime power that is not a prime cost at most
  `2 log n (ψ(n) − θ(n))`, and odd `n` carry at most `2 log 2 log n`;
* `window_even_goldbach`: under RH, for `N ≥ N₀` and `C log² N ≤ H ≤ N` some even
  `n ∈ [N − H, N + H]` is a sum of two primes;
* `kataiMV_proved : RiemannHypothesis → KataiMV`, `linnik_proved : RiemannHypothesis → LinnikRH`.

KNOWN mathematics, Linnik 1952, Kátai 1967, Montgomery-Vaughan 1975; the chain here runs through
the lab's own Selberg, Cramér and Languasco-Zaccagnini files.
-/

namespace LeanLab.LZCesaroShort

open Finset Filter
open scoped ArithmeticFunction.vonMangoldt Chebyshev

set_option maxHeartbeats 4000000 in
/-- `cesaro_pos_of_printed` with its quantitative conclusion `HN/8 ≤ cesaro N H`. -/
theorem cesaro_ge_of_printed (h1 : Theorem1P) (h5 : Sec5RH) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ, N₀ ≤ N → C * Real.log N ^ 2 ≤ H → H ≤ N →
      (H : ℝ) * N / 8 ≤ cesaro N H := by
  obtain ⟨K1', hK1⟩ := h1
  obtain ⟨N5, K2', hK2⟩ := h5
  set K1 := |K1'|
  set K2 := |K2'|
  have K1n : 0 ≤ K1 := abs_nonneg _
  have K2n : 0 ≤ K2 := abs_nonneg _
  obtain ⟨Ne, hNe⟩ := eventually_atTop.mp (eventually_small (2 * K1 + 2 * K2))
  refine ⟨32 * K1 + 8 * K2 + 4, max (max Ne N5) 3, fun N H hN hCH hHN => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 ≤ Real.log N := by linarith
  have hL2 : 1 ≤ Real.log N ^ 2 := by nlinarith
  have hHR : (4 : ℝ) ≤ H := by
    have : (4 : ℝ) * 1 ≤ (32 * K1 + 8 * K2 + 4) * Real.log N ^ 2 :=
      mul_le_mul (by linarith) hL2 (by norm_num) (by linarith)
    linarith
  have hH2 : 2 ≤ H := by exact_mod_cast (show (2 : ℝ) ≤ H by linarith)
  have hH1 : 1 ≤ H := by omega
  have hHle : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hHp : (0 : ℝ) < H := by linarith
  obtain ⟨hs1, hs2⟩ := hNe N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have b1 := hK1 N H (by omega) hH1 hHN
  have b2 := hK2 N H (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) hH2 hHN
  -- logs
  have hlogA : Real.log (2 * (N : ℝ) / H) ≤ 2 * Real.log N := by
    have : 2 * (N : ℝ) / H ≤ (N : ℝ) ^ 2 := by
      rw [div_le_iff₀ hHp]; nlinarith
    calc _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlogA0 : 0 ≤ Real.log (2 * (N : ℝ) / H) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hHp]; linarith
  have hlogA2 : Real.log (2 * (N : ℝ) / H) ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
  have hlogB : Real.log (2 * (H : ℝ)) ≤ 2 * Real.log N := by
    have : 2 * (H : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    calc _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlogB0 : 0 ≤ Real.log (2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have X1n : 0 ≤ (N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2
      + H * Real.log N ^ 2 * Real.log (2 * H) := by positivity
  have b1' : ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
      ≤ K1 * (N * Real.log (2 * (N : ℝ) / H) ^ 2 + H * Real.log N ^ 2 * Real.log (2 * H)) :=
    le_trans b1 (mul_le_mul_of_nonneg_right (le_abs_self K1') X1n)
  have X2n : 0 ≤ (H : ℝ) * Real.sqrt N * Real.log N ^ 2 + N := by positivity
  have b2' : ‖ZH N H / (H : ℂ)‖ ≤ K2 * (H * Real.sqrt N * Real.log N ^ 2 + N) :=
    le_trans b2 (mul_le_mul_of_nonneg_right (le_abs_self K2') X2n)
  set E : ℂ := 2 / (H : ℂ) * ZH N H
  have hE : ‖E‖ ≤ 2 * (K2 * ((H : ℝ) * Real.sqrt N * Real.log N ^ 2 + N)) := by
    have : E = 2 * (ZH N H / (H : ℂ)) := by simp only [E]; ring
    rw [this, norm_mul]; simp only [Complex.norm_ofNat]; linarith
  have hreal : (H : ℝ) * N - cesaro N H ≤ ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + E‖ + ‖E‖ := by
    have e : (((H : ℝ) * N - cesaro N H : ℝ) : ℂ)
        = -((((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + E)) + E := by push_cast; ring
    calc (H : ℝ) * N - cesaro N H ≤ ‖((((H : ℝ) * N - cesaro N H : ℝ)) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ _ := by rw [e]; exact le_trans (norm_add_le _ _) (by rw [norm_neg])
  have hCL : (32 * K1 + 8 * K2 + 4) * Real.log N ^ 2 * N ≤ H * N :=
    mul_le_mul_of_nonneg_right hCH (by positivity)
  -- the error terms
  have t1 : K1 * (N * Real.log (2 * (N : ℝ) / H) ^ 2) ≤ 4 * K1 * N * Real.log N ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlogA2 (show 0 ≤ K1 * N by positivity); linarith
  have t2 : K1 * (H * Real.log N ^ 2 * Real.log (2 * H)) ≤ 2 * K1 * H * Real.log N ^ 3 := by
    have := mul_le_mul_of_nonneg_left hlogB (show 0 ≤ K1 * H * Real.log N ^ 2 by positivity)
    have e : K1 * H * Real.log N ^ 2 * (2 * Real.log N) = 2 * K1 * H * Real.log N ^ 3 := by ring
    linarith
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
  have hsqn : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have t3 : 2 * K1 * H * Real.log N ^ 3 ≤ H * N / 4 := by
    have : 2 * K1 * Real.log N ^ 3 ≤ N / 4 := by
      have : 2 * K1 * Real.log N ^ 3 ≤ (2 * K1 + 2 * K2) * Real.log N ^ 3 := by
        nlinarith [pow_nonneg hL0 3]
      linarith
    have := mul_le_mul_of_nonneg_left this hHp.le
    have e : (H : ℝ) * (2 * K1 * Real.log N ^ 3) = 2 * K1 * H * Real.log N ^ 3 := by ring
    linarith
  have t4 : 2 * K2 * (H * Real.sqrt N * Real.log N ^ 2) ≤ H * N / 4 := by
    have hs : 2 * K2 * Real.log N ^ 2 ≤ Real.sqrt N / 4 := by
      have : 2 * K2 * Real.log N ^ 2 ≤ (2 * K1 + 2 * K2) * Real.log N ^ 2 := by
        nlinarith [pow_nonneg hL0 2]
      linarith
    have := mul_le_mul_of_nonneg_left hs (show 0 ≤ (H : ℝ) * Real.sqrt N by positivity)
    have e1 : (H : ℝ) * Real.sqrt N * (Real.sqrt N / 4) = H * N / 4 := by
      rw [mul_assoc, ← mul_div_assoc, hsq]; ring
    have e2 : (H : ℝ) * Real.sqrt N * (2 * K2 * Real.log N ^ 2)
        = 2 * K2 * (H * Real.sqrt N * Real.log N ^ 2) := by ring
    linarith
  have t1' : 4 * K1 * N * Real.log N ^ 2 ≤ H * N / 8 := by
    have h8 : 32 * K1 * Real.log N ^ 2 * N ≤ (32 * K1 + 8 * K2 + 4) * Real.log N ^ 2 * N := by
      have : 0 ≤ (8 * K2 + 4) * Real.log N ^ 2 * N := by positivity
      nlinarith
    nlinarith
  have t5 : 2 * K2 * (N : ℝ) ≤ H * N / 4 := by
    have h8 : 8 * K2 * N ≤ (32 * K1 + 8 * K2 + 4) * Real.log N ^ 2 * N := by
      have : 8 * K2 * N * 1 ≤ 8 * K2 * N * Real.log N ^ 2 :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
      have : 0 ≤ (32 * K1 + 4) * Real.log N ^ 2 * N := by positivity
      nlinarith
    nlinarith
  have hfin : (H : ℝ) * N - cesaro N H ≤ 7 * (H * N) / 8 := by
    have e1 : K1 * ((N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2
        + H * Real.log N ^ 2 * Real.log (2 * H))
        = K1 * (N * Real.log (2 * (N : ℝ) / H) ^ 2) + K1 * (H * Real.log N ^ 2 * Real.log (2 * H)) :=
      by ring
    have e2 : 2 * (K2 * ((H : ℝ) * Real.sqrt N * Real.log N ^ 2 + N))
        = 2 * K2 * (H * Real.sqrt N * Real.log N ^ 2) + 2 * K2 * N := by ring
    linarith
  linarith

/-- The prime pair part of `R`. -/
noncomputable def Rp (n : ℕ) : ℝ :=
  ∑ p ∈ antidiagonal n, if p.1.Prime ∧ p.2.Prime then Λ p.1 * Λ p.2 else 0

lemma Rp_nonneg (n : ℕ) : 0 ≤ Rp n :=
  sum_nonneg fun p _ => by
    split_ifs
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl

lemma goldbach_of_Rp_pos {n : ℕ} (h : 0 < Rp n) : IsGoldbachSum n := by
  by_contra hc
  have : Rp n = 0 := by
    refine sum_eq_zero fun p hp => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hc ⟨p.1, p.2, h1, h2, (mem_antidiagonal.mp hp)⟩
  linarith

lemma sum_not_prime_eq (n : ℕ) :
    ∑ k ∈ range (n + 1), (if ¬ k.Prime then Λ k else 0) = ψ (n : ℝ) - θ (n : ℝ) := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter, range_eq_Ico,
    sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [Nat.not_prime_zero, not_false_eq_true, if_true, ArithmeticFunction.map_zero, zero_add]
  rfl

lemma R_sub_Rp_le {n : ℕ} (hn : 1 ≤ n) : R n - Rp n ≤ 2 * Real.log n * (ψ (n : ℝ) - θ (n : ℝ)) := by
  have hlog : ∀ k, k ≤ n → Λ k ≤ Real.log n := fun k hk => vonMangoldt_le_log_of_le hk
  have hpt : ∀ p ∈ antidiagonal n, Λ p.1 * Λ p.2 - (if p.1.Prime ∧ p.2.Prime then Λ p.1 * Λ p.2 else 0)
      ≤ (if ¬ p.1.Prime then Λ p.1 else 0) * Real.log n + (if ¬ p.2.Prime then Λ p.2 else 0) * Real.log n := by
    intro p hp
    have hs := mem_antidiagonal.mp hp
    have h1 := hlog p.1 (by omega)
    have h2 := hlog p.2 (by omega)
    have a0 := ArithmeticFunction.vonMangoldt_nonneg (n := p.1)
    have b0 := ArithmeticFunction.vonMangoldt_nonneg (n := p.2)
    by_cases ha : p.1.Prime <;> by_cases hb : p.2.Prime <;> simp [ha, hb] <;> nlinarith
  unfold R Rp
  rw [← sum_sub_distrib]
  refine (sum_le_sum hpt).trans (le_of_eq ?_)
  rw [sum_add_distrib, ← sum_mul, ← sum_mul]
  have e1 : ∑ p ∈ antidiagonal n, (if ¬ p.1.Prime then Λ p.1 else 0) = ψ (n : ℝ) - θ (n : ℝ) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a _ => if ¬ a.Prime then Λ a else 0)]
    exact sum_not_prime_eq n
  have e2 : ∑ p ∈ antidiagonal n, (if ¬ p.2.Prime then Λ p.2 else 0) = ψ (n : ℝ) - θ (n : ℝ) := by
    rw [← Finset.Nat.sum_antidiagonal_swap]
    simp only [Prod.fst_swap, Prod.snd_swap]
    exact e1
  rw [e1, e2]; ring

lemma Rp_odd_le {n : ℕ} (hn : Odd n) : Rp n ≤ 2 * (Real.log 2 * Real.log n) := by
  have hl2 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
  have hln : (0:ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  have c0 : 0 ≤ Real.log 2 * Real.log n := mul_nonneg hl2 hln
  have hL2 : Λ 2 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; norm_num
  have hpt : ∀ p ∈ antidiagonal n, (if p.1.Prime ∧ p.2.Prime then Λ p.1 * Λ p.2 else 0)
      ≤ (if p.1 = 2 then Real.log 2 * Real.log n else 0) + (if p.2 = 2 then Real.log 2 * Real.log n else 0) := by
    intro p hp
    have hs := mem_antidiagonal.mp hp
    have hA0 : 0 ≤ (if p.1 = 2 then Real.log 2 * Real.log n else 0) := by split_ifs <;> linarith
    have hB0 : 0 ≤ (if p.2 = 2 then Real.log 2 * Real.log n else 0) := by split_ifs <;> linarith
    by_cases h : p.1.Prime ∧ p.2.Prime
    · rw [if_pos h]
      have h1 : Λ p.1 ≤ Real.log n := vonMangoldt_le_log_of_le (by omega)
      have h2 : Λ p.2 ≤ Real.log n := vonMangoldt_le_log_of_le (by omega)
      have a0 := ArithmeticFunction.vonMangoldt_nonneg (n := p.1)
      have b0 := ArithmeticFunction.vonMangoldt_nonneg (n := p.2)
      by_cases hA : p.1 = 2
      · rw [if_pos hA]
        have e : Λ p.1 = Real.log 2 := by rw [hA, hL2]
        rw [e]; nlinarith
      · by_cases hB : p.2 = 2
        · rw [if_neg hA, if_pos hB]
          have e : Λ p.2 = Real.log 2 := by rw [hB, hL2]
          rw [e]; nlinarith
        · exfalso
          have o1 := h.1.odd_of_ne_two hA
          have o2 := h.2.odd_of_ne_two hB
          have : Even (p.1 + p.2) := o1.add_odd o2
          rw [hs] at this
          exact (Nat.not_even_iff_odd.mpr hn) this
    · rw [if_neg h]; linarith
  unfold Rp
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib]
  have c0 : (0 : ℝ) ≤ Real.log 2 * Real.log n := by
    have : (0:ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
    have := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    positivity
  have hone : ∀ (f : ℕ × ℕ → ℕ), (∀ p ∈ antidiagonal n, ∀ q ∈ antidiagonal n, f p = 2 → f q = 2 → p = q) →
      ∑ p ∈ antidiagonal n, (if f p = 2 then Real.log 2 * Real.log n else 0) ≤ Real.log 2 * Real.log n := by
    intro f hf
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have : ((antidiagonal n).filter (fun p => f p = 2)).card ≤ 1 := by
      rw [card_le_one]
      intro p hp q hq
      simp only [mem_filter] at hp hq
      exact hf p hp.1 q hq.1 hp.2 hq.2
    have : (((antidiagonal n).filter (fun p => f p = 2)).card : ℝ) ≤ 1 := by exact_mod_cast this
    nlinarith
  have s1 := hone Prod.fst (fun p hp q hq h1 h2 => by
    have a := mem_antidiagonal.mp hp; have b := mem_antidiagonal.mp hq
    exact Prod.ext (h1.trans h2.symm) (by omega))
  have s2 := hone Prod.snd (fun p hp q hq h1 h2 => by
    have a := mem_antidiagonal.mp hp; have b := mem_antidiagonal.mp hq
    exact Prod.ext (by omega) (h1.trans h2.symm))
  linarith

/-- `R(n) ≤ 32 √N log² N + 4 log 2 log N` on the window when no even `n` there is a sum of two
primes; the bound behind `window_even_goldbach`. -/
lemma R_le_window {N H n : ℕ} (hN : 2 ≤ N) (hHN : H ≤ N) (hn : n ≤ N + H)
    (hno : Even n → ¬ IsGoldbachSum n) :
    R n ≤ 32 * Real.sqrt N * Real.log N ^ 2 + 4 * Real.log 2 * Real.log N := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hn2 : (n : ℝ) ≤ 2 * N := by
    have : (n : ℝ) ≤ N + H := by exact_mod_cast hn
    have : (H : ℝ) ≤ N := by exact_mod_cast hHN
    linarith
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hl2 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
  have hsN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : R 0 = 0 := by simp [R]
    rw [this]; positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
  have hlogn : Real.log n ≤ 2 * Real.log N := by
    have : (n : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    calc Real.log n ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by linarith) this
      _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hsqn : Real.sqrt n ≤ 2 * Real.sqrt N := by
    have : Real.sqrt n ≤ Real.sqrt (4 * N) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have h1 := R_sub_Rp_le hpos
  have h2 := Chebyshev.psi_sub_theta_le hn1
  have h3 : R n - Rp n ≤ 32 * Real.sqrt N * Real.log N ^ 2 := by
    have : 2 * Real.log n * (ψ (n : ℝ) - θ (n : ℝ)) ≤ 2 * Real.log n * (2 * Real.sqrt n * Real.log n) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have hsq : Real.log n ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
    have : 2 * Real.log n * (2 * Real.sqrt n * Real.log n) = 4 * Real.sqrt n * Real.log n ^ 2 := by ring
    have : 4 * Real.sqrt n * Real.log n ^ 2 ≤ 4 * (2 * Real.sqrt N) * (4 * Real.log N ^ 2) :=
      mul_le_mul (by linarith) hsq (sq_nonneg _) (by positivity)
    nlinarith
  have h4 : Rp n ≤ 4 * Real.log 2 * Real.log N := by
    rcases Nat.even_or_odd n with he | ho
    · have : Rp n = 0 := by
        rcases (Rp_nonneg n).lt_or_eq with hlt | heq
        · exact absurd (goldbach_of_Rp_pos hlt) (hno he)
        · exact heq.symm
      rw [this]; positivity
    · have := Rp_odd_le ho
      nlinarith
  linarith

set_option maxHeartbeats 4000000 in
/-- **An even sum of two primes in every window `C log² N ≤ H ≤ N`, under RH.** -/
theorem window_even_goldbach (hRH : RiemannHypothesis) : ∃ C : ℝ, ∃ N₀ : ℕ,
    ∀ N H : ℕ, N₀ ≤ N → C * Real.log N ^ 2 ≤ H → H ≤ N →
      ∃ n ∈ Icc (N - H) (N + H), Even n ∧ IsGoldbachSum n := by
  obtain ⟨C, N₁, hc⟩ := cesaro_ge_of_printed (theorem1P_proved hRH) (lz_sec5_rh_proved hRH)
  obtain ⟨Ne, hNe⟩ := eventually_atTop.mp (eventually_small 3456)
  refine ⟨max C 1, max (max N₁ Ne) 3, fun N H hN hCH hHN => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL2 : 1 ≤ Real.log N ^ 2 := by nlinarith
  have hH1r : (1 : ℝ) ≤ H := by
    have : (1 : ℝ) * 1 ≤ max C 1 * Real.log N ^ 2 :=
      mul_le_mul (le_max_right _ _) hL2 (by norm_num) (by positivity)
    linarith
  have hH : 1 ≤ H := by exact_mod_cast hH1r
  have hCH' : C * Real.log N ^ 2 ≤ H :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hCH
  have hge := hc N H (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) hCH' hHN
  by_contra hno
  push_neg at hno
  set B := 32 * Real.sqrt N * Real.log N ^ 2 + 4 * Real.log 2 * Real.log N with hB
  have hpt : ∀ n ∈ Icc (N - H) (N + H), w N H n * R n ≤ B := by
    intro n hn
    have hm := mem_Icc.mp hn
    have hw := w_mem hH hm.1 hm.2 hHN
    have hR := R_le_window (by omega) hHN hm.2 (fun he hg => hno n hn he hg)
    have := R_nonneg n
    nlinarith
  have hsum : cesaro N H ≤ (2 * H + 1) * B := by
    unfold cesaro
    refine (sum_le_sum hpt).trans (le_of_eq ?_)
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
    congr 1
    have : N + H + 1 - (N - H) = 2 * H + 1 := by omega
    rw [this]; push_cast; ring
  obtain ⟨_, hs2⟩ := hNe N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hs1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; linarith
  have hl2 := Real.log_two_lt_d9
  have hl20 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
  have hBle : B ≤ 36 * Real.sqrt N * Real.log N ^ 2 := by
    have : 4 * Real.log 2 * Real.log N ≤ 4 * Real.sqrt N * Real.log N ^ 2 := by
      have : Real.log N ≤ Real.log N ^ 2 := by nlinarith
      have : Real.log 2 * Real.log N ≤ 1 * Real.log N := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have : Real.log N ^ 2 ≤ Real.sqrt N * Real.log N ^ 2 := le_mul_of_one_le_left (by positivity) hs1
      nlinarith
    rw [hB]; linarith
  have hfin : 36 * Real.sqrt N * Real.log N ^ 2 * 3 < N / 8 := by
    have : 108 * Real.log N ^ 2 ≤ Real.sqrt N / 128 := by nlinarith
    have hsN0' : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have := mul_le_mul_of_nonneg_left this hsN0'
    nlinarith
  have hH3 : (2 * (H : ℝ) + 1) ≤ 3 * H := by linarith
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have : cesaro N H ≤ 3 * H * B := hsum.trans (mul_le_mul_of_nonneg_right hH3 hB0)
  have : 3 * (H : ℝ) * B ≤ H * (36 * Real.sqrt N * Real.log N ^ 2 * 3) := by nlinarith
  have : (H : ℝ) * (36 * Real.sqrt N * Real.log N ^ 2 * 3) < H * (N / 8) :=
    mul_lt_mul_of_pos_left hfin (by linarith)
  nlinarith

end LeanLab.LZCesaroShort

namespace LeanLab.GoldbachGaps.Goldston1990

open Finset

set_option maxHeartbeats 2000000 in
/-- **Kátai, Montgomery-Vaughan from RH alone.** -/
theorem kataiMV_proved (hRH : RiemannHypothesis) : KataiMV := by
  obtain ⟨C, N₀, hw⟩ := LeanLab.LZCesaroShort.window_even_goldbach hRH
  set C' := |C| + 1 with hC'
  have hC'1 : 1 ≤ C' := by have := abs_nonneg C; linarith
  refine ⟨8 * C' + 5, by positivity, max (N₀ : ℝ) (16 * C' + 7), fun N hN => ?_⟩
  have hNN₀ : (N₀ : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  have hN7 : 16 * C' + 7 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9; linarith
  have hL2 : 1 ≤ Real.log N ^ 2 := by nlinarith
  have hlog4 : Real.log N ^ 2 ≤ 4 * N := by
    have h := LeanLab.PNTPort.Selberg.log_le_two_sqrt hN0
    have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
    have : Real.log N ^ 2 ≤ (2 * Real.sqrt N) ^ 2 := pow_le_pow_left₀ (by linarith) h 2
    nlinarith
  set H : ℕ := ⌈4 * C' * Real.log N ^ 2⌉₊ + 1 with hH
  have hHlo : 4 * C' * Real.log N ^ 2 ≤ H := by
    rw [hH]; push_cast; linarith [Nat.le_ceil (4 * C' * Real.log N ^ 2)]
  have hHhi : (H : ℝ) ≤ 4 * C' * Real.log N ^ 2 + 2 := by
    rw [hH]; push_cast; linarith [Nat.ceil_lt_add_one (show 0 ≤ 4 * C' * Real.log N ^ 2 by positivity)]
  set c := ⌈N⌉₊ with hc
  have hc1 : N ≤ c := Nat.le_ceil N
  have hc2 : (c : ℝ) < N + 1 := Nat.ceil_lt_add_one hN0.le
  set M : ℕ := c + H with hM
  have hMr : (M : ℝ) = c + H := by rw [hM]; push_cast; ring
  have hM1 : (1 : ℝ) ≤ M := by rw [hMr]; have : (0 : ℝ) ≤ H := Nat.cast_nonneg H; linarith
  have hMsq : (M : ℝ) ≤ N ^ 2 := by
    rw [hMr]
    have : 4 * C' * Real.log N ^ 2 ≤ 4 * C' * (4 * N) := mul_le_mul_of_nonneg_left hlog4 (by positivity)
    nlinarith
  have hlogM : Real.log M ≤ 2 * Real.log N := by
    calc Real.log M ≤ Real.log (N ^ 2) := Real.log_le_log (by linarith) hMsq
      _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hCH : C * Real.log M ^ 2 ≤ H := by
    have h1 : C * Real.log M ^ 2 ≤ |C| * Real.log M ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)
    have h2 : Real.log M ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
    have h3 : |C| * Real.log M ^ 2 ≤ |C| * (4 * Real.log N ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    have h4 : |C| * (4 * Real.log N ^ 2) ≤ 4 * C' * Real.log N ^ 2 := by
      rw [hC']; nlinarith [abs_nonneg C]
    linarith
  have hMN₀ : N₀ ≤ M := by
    have : (N₀ : ℝ) ≤ M := by rw [hMr]; have : (0 : ℝ) ≤ H := Nat.cast_nonneg H; linarith
    exact_mod_cast this
  obtain ⟨n, hn, he, hg⟩ := hw M H hMN₀ hCH (by omega)
  have hn' := mem_Icc.mp hn
  have hlo : (c : ℝ) ≤ n := by
    have : c ≤ n := by have := hn'.1; omega
    exact_mod_cast this
  have hhi : (n : ℝ) ≤ c + 2 * H := by
    have : n ≤ c + 2 * H := by have := hn'.2; omega
    exact_mod_cast this
  refine ⟨n, ⟨he, hg⟩, hc1.trans hlo, hhi.trans ?_⟩
  nlinarith

/-- **Linnik's form from RH alone.** -/
theorem linnik_proved (hRH : RiemannHypothesis) : LinnikRH :=
  linnikRH_of_kataiMV (kataiMV_proved hRH)

end LeanLab.GoldbachGaps.Goldston1990
