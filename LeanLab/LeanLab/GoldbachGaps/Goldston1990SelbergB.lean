import LeanLab.GoldbachGaps.Goldston1990Selberg
import LeanLab.PNTPort.Selberg.AdditiveBlocksB

/-!
# Goldston's variance under RH in his own range

Lab proof, unit U-6015, CLOUD 20261020T0415Z-cloud34, T2, P0030 and IDEAS I-5100. AI wrote
this file. CONDITIONAL ON RiemannHypothesis only, through `PNTPort.Selberg.selberg_sum_b`.

* `jg_rh_b`: under RH, for naturals `h ≥ 1` with `h² ≤ N`,
  `J(N, h) ≤ C (h N (log(N/h) + 3)² + N (log N + 2)²/√h)`, Selberg's `J ≪ h N log² N`;
* `jg_little_o_b`: under RH, `J(N, K_N) = o(K_N² N)` whenever `log² N/K_N → 0` and `K_N² ≤ N`;
* `corollary1_rh_b`, `corollary2_rh_b`: Goldston's Corollaries 1 and 2 under RH for every such
  `K_N`, CONDITIONAL ON the cited Corollaries themselves, whose hypothesis `J = o(K² N)` is now
  a theorem under RH on Goldston's whole range `K/log² N → ∞`.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset Filter MeasureTheory

set_option maxHeartbeats 1000000 in
/-- **Goldston's variance under RH, from Selberg's mean square.** -/
theorem jg_rh_b (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N h : ℕ, 1 ≤ h → h * h ≤ N →
    Jg N h ≤ C * (h * N * (Real.log (N / h) + 3) ^ 2 + N * ((Real.log N + 2) ^ 2 / Real.sqrt h)) := by
  obtain ⟨C1, hC1, hs⟩ := LeanLab.PNTPort.Selberg.selberg_sum_b hRH
  refine ⟨4 * C1 + 64, by positivity, fun N h hh hhN => ?_⟩
  have hhN' : h ≤ N := le_trans (Nat.le_mul_self h) hhN
  have hN : 1 ≤ N := hh.trans hhN'
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hhNr : (h : ℝ) ≤ N := by exact_mod_cast hhN'
  have hhhN : (h : ℝ) * h ≤ N := by exact_mod_cast hhN
  set ℓ := Real.log (N / h) + 3 with hℓ
  have hlog0 : 0 ≤ Real.log (N / h) := Real.log_nonneg (by rw [le_div_iff₀ hh0]; linarith)
  have hℓ3 : 3 ≤ ℓ := by linarith
  set P := N * ((Real.log N + 2) ^ 2 / Real.sqrt h) with hP
  have hP0 : 0 ≤ P := by positivity
  rw [jg_eq_sum hN]
  -- the split
  have hpt : ∀ m : ℕ, (θ ((m : ℝ) + h) - θ m - h) ^ 2 ≤
      2 * (ψ ((m : ℝ) + h) - ψ m - h) ^ 2 +
        2 * ((ψ ((m : ℝ) + h) - θ ((m : ℝ) + h)) - (ψ m - θ m)) ^ 2 := by
    intro m
    nlinarith [sq_nonneg ((ψ ((m : ℝ) + h) - ψ m - h) + ((ψ ((m : ℝ) + h) - θ ((m : ℝ) + h)) - (ψ m - θ m)))]
  have hA : ∑ m ∈ Ico 1 N, (ψ ((m : ℝ) + h) - ψ m - h) ^ 2 ≤
      C1 * (N * h * ℓ ^ 2 + P + (h : ℝ) ^ 3) := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (fun m hm => by
      simp only [mem_Ico, mem_range] at hm ⊢; omega) (fun m _ _ => sq_nonneg _)) (hs N h N hh hhN' le_rfl)
  have hB := sum_psi_sub_theta_sq N h
  -- `log(N + h) ≤ 2ℓ`
  have hlogNh : Real.log ((N : ℝ) + h) ≤ 2 * ℓ := by
    have h1 : Real.log ((N : ℝ) + h) ≤ Real.log (2 * N) := Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N := Real.log_mul (by norm_num) (by positivity)
    have h3 : Real.log (N : ℝ) = Real.log (N / h) + Real.log h := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    have h4 : 2 * Real.log (h : ℝ) ≤ Real.log N := by
      rw [← Real.log_rpow hh0, Real.rpow_two]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have h5 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hlogNh0 : 0 ≤ Real.log ((N : ℝ) + h) := Real.log_nonneg (by linarith)
  have hB' : 4 * h * (N + h) * Real.log (N + h) ^ 2 ≤ 32 * (h * N * ℓ ^ 2) := by
    have e1 : Real.log ((N : ℝ) + h) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
    have e2 : (N : ℝ) + h ≤ 2 * N := by linarith
    have : (4 : ℝ) * h * (N + h) ≤ 4 * h * (2 * N) := by gcongr
    calc 4 * h * (N + h) * Real.log (N + h) ^ 2 ≤ 4 * h * (2 * N) * (4 * ℓ ^ 2) :=
          mul_le_mul this e1 (sq_nonneg _) (by positivity)
      _ = 32 * (h * N * ℓ ^ 2) := by ring
  have hh3 : (h : ℝ) ^ 3 ≤ h * N * ℓ ^ 2 := by
    have : (h : ℝ) ^ 3 ≤ h * N := by nlinarith
    have : (h : ℝ) * N ≤ h * N * ℓ ^ 2 := by
      have : 1 ≤ ℓ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ h * N)]
    linarith
  have hX0 : 0 ≤ (h : ℝ) * N * ℓ ^ 2 := by positivity
  calc ∑ m ∈ Ico 1 N, (θ ((m : ℝ) + h) - θ m - h) ^ 2
      ≤ ∑ m ∈ Ico 1 N, (2 * (ψ ((m : ℝ) + h) - ψ m - h) ^ 2 +
          2 * ((ψ ((m : ℝ) + h) - θ ((m : ℝ) + h)) - (ψ m - θ m)) ^ 2) := sum_le_sum fun m _ => hpt m
    _ = 2 * ∑ m ∈ Ico 1 N, (ψ ((m : ℝ) + h) - ψ m - h) ^ 2 +
          2 * ∑ m ∈ Ico 1 N, ((ψ ((m : ℝ) + h) - θ ((m : ℝ) + h)) - (ψ m - θ m)) ^ 2 := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ 2 * (C1 * (N * h * ℓ ^ 2 + P + (h : ℝ) ^ 3)) + 2 * (32 * (h * N * ℓ ^ 2)) := by
        gcongr; exact hB.trans hB'
    _ ≤ (4 * C1 + 64) * (h * N * ℓ ^ 2 + P) := by
        have e : (N : ℝ) * h * ℓ ^ 2 = h * N * ℓ ^ 2 := by ring
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_left hh3 hC1, mul_nonneg hC1 hX0, mul_nonneg hC1 hP0]

set_option maxHeartbeats 1000000 in
/-- **`J(N, K) = o(K² N)` under RH whenever `log² N = o(K)`**, Goldston's range. -/
theorem jg_little_o_b (hRH : RiemannHypothesis) (K : ℕ → ℕ)
    (hlog : Tendsto (fun N : ℕ => Real.log N ^ 2 / K N) atTop (nhds 0))
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ K N * K N ≤ N) :
    Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) := by
  obtain ⟨C, hC, hj⟩ := jg_rh_b hRH
  have hg : Tendsto (fun N : ℕ => 30 * C * (Real.log N ^ 2 / K N)) atTop (nhds 0) := by
    simpa using hlog.const_mul (30 * C)
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N := by
    have := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 1))
    filter_upwards [this] with N hN
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hN)]; exact hN
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards [hK, eventually_ge_atTop 1] with N hN hN1
    have hJ0 : 0 ≤ Jg N (K N) := by
      rw [jg_eq_sum hN1]; exact sum_nonneg fun m _ => sq_nonneg _
    exact div_nonneg hJ0 (by positivity)
  · filter_upwards [hK, eventually_ge_atTop 1, hlogN] with N hN hN1 hl1
    obtain ⟨hK1, hKN⟩ := hN
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < N := by linarith
    have hK1r : (1 : ℝ) ≤ K N := by exact_mod_cast hK1
    have hK0 : (0 : ℝ) < K N := by linarith
    have hKNr : (K N : ℝ) ≤ N := by
      have : (K N : ℝ) * K N ≤ N := by exact_mod_cast hKN
      nlinarith
    have hb := hj N (K N) hK1 hKN
    set l := Real.log N with hl
    set ℓ := Real.log (N / K N) + 3 with hℓ
    have hl0 : 0 ≤ Real.log (N / K N) := Real.log_nonneg (by rw [le_div_iff₀ hK0]; linarith)
    have hl1' : Real.log (N / K N) ≤ l := Real.log_le_log (by positivity) (div_le_self hN0.le hK1r)
    have hsK : 1 ≤ Real.sqrt (K N) := Real.one_le_sqrt.mpr hK1r
    have hden : 0 < (K N : ℝ) ^ 2 * N := by positivity
    rw [div_le_iff₀ hden]
    have t1 : (K N : ℝ) * N * ℓ ^ 2 ≤ 16 * l ^ 2 * ((K N : ℝ) * N) := by
      have : ℓ ≤ 4 * l := by linarith
      have : ℓ ^ 2 ≤ 16 * l ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (K N : ℝ) * N)]
    have t2 : (N : ℝ) * ((l + 2) ^ 2 / Real.sqrt (K N)) ≤ 9 * l ^ 2 * N := by
      have h1 : (l + 2) ^ 2 / Real.sqrt (K N) ≤ (l + 2) ^ 2 := div_le_self (by positivity) hsK
      have h2 : (l + 2) ^ 2 ≤ 9 * l ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hN0.le]
    have e : 30 * C * (l ^ 2 / K N) * ((K N : ℝ) ^ 2 * N) = 30 * C * (l ^ 2 * ((K N : ℝ) * N)) := by
      field_simp
    rw [e]
    calc Jg N (K N) ≤ C * ((K N : ℝ) * N * ℓ ^ 2 + N * ((l + 2) ^ 2 / Real.sqrt (K N))) := hb
      _ ≤ C * (16 * l ^ 2 * ((K N : ℝ) * N) + 9 * l ^ 2 * N) := by gcongr
      _ ≤ C * (16 * l ^ 2 * ((K N : ℝ) * N) + 9 * l ^ 2 * ((K N : ℝ) * N)) := by
          gcongr
          nlinarith
      _ ≤ 30 * C * (l ^ 2 * ((K N : ℝ) * N)) := by
          have : 0 ≤ C * (l ^ 2 * ((K N : ℝ) * N)) := by positivity
          nlinarith

/-- `K_N² ≤ N` puts `K_N` below `N/log³ N` eventually. -/
lemma range_of_sq_le (K : ℕ → ℕ) (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ K N * K N ≤ N) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3 := by
  filter_upwards [hK, eventually_sqrt_le] with N hN hs
  refine ⟨hN.1, le_trans ?_ hs⟩
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have : ((K N * K N : ℕ) : ℝ) ≤ N := by exact_mod_cast hN.2
  push_cast at this; nlinarith

/-- **Goldston's Corollary 1 under RH on his whole range**, CONDITIONAL ON the cited Corollary 1. -/
theorem corollary1_rh_b (hRH : RiemannHypothesis) (hC1 : Corollary1) (K : ℕ → ℕ)
    (hlog : Tendsto (fun N : ℕ => Real.log N ^ 2 / K N) atTop (nhds 0))
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ K N * K N ≤ N) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) / ((K N : ℝ) * N / Real.log N ^ 2))
      atTop (nhds 1) :=
  hC1 K (range_of_sq_le K hK) (jg_little_o_b hRH K hlog hK)

/-- **Goldston's Corollary 2 under RH on his whole range**, CONDITIONAL ON the cited
Corollary 2: a positive proportion of `[N, N + K]` are Goldbach numbers. -/
theorem corollary2_rh_b (hRH : RiemannHypothesis) (hC2 : Corollary2) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ → ℕ,
      Tendsto (fun N : ℕ => Real.log N ^ 2 / K N) atTop (nhds 0) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ K N * K N ≤ N) →
      ∀ᶠ N : ℕ in atTop, c * K N ≤ (((Icc N (N + K N)).filter (fun n => 1 ≤ rg n)).card : ℝ) := by
  obtain ⟨C, c, hC, hc, h⟩ := hC2
  refine ⟨c, hc, fun K hlog hK => h K ?_ (jg_little_o_b hRH K hlog hK)⟩
  have hev := hlog.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / C by positivity))
  filter_upwards [hev, range_of_sq_le K hK] with N h1 h2
  refine ⟨?_, h2.2⟩
  have hK0 : (0 : ℝ) < K N := by have := h2.1; exact_mod_cast this
  rw [div_lt_div_iff₀ hK0 hC] at h1
  linarith

end LeanLab.GoldbachGaps.Goldston1990
