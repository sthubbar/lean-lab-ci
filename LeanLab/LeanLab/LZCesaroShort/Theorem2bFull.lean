import LeanLab.LZCesaroShort.Theorem2aFull

/-!
# P0058 Theorem 2 eq. (3) from RH for every `1 ≤ H ≤ N`

Lab proof, unit U-6204, CLOUD 20261020T0817Z-cloud38, T1. AI wrote this file. CONDITIONAL ON
RiemannHypothesis only, through `lemma1_full`. Binary Goldbach is OPEN.

* `integral_norm_le_sqrt_sym`: `∫_{-ξ}^{ξ} ‖g‖ ≤ √(2ξ B)` when `∫_{-ξ}^{ξ} ‖g‖² ≤ B`;
* `I3_bound_full`: eq. (30) for every `1 ≤ H ≤ N`;
* `I2_bound_fine`: `I₂` at `y = H` with error `2(K₂ H √N (1 + log(2N/H)) + 8√(H³(1 + N/2)) + H²)`,
  the piece with `S̃ − 1/z` by the dyadic layers of `Layer.lean` and Lemma 1 on each window, the
  piece with `W` by Cauchy-Schwarz and `TH_L2`;
* `theorem2b_full`: **under RH**, for `N ≥ 10^20` and every `1 ≤ H ≤ N`,
  `|wsum N H H| ≤ K N (log(2N/H))²`, P0058 Theorem 2 eq. (3) as printed.
-/

namespace LeanLab.LZCesaroShort

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Chebyshev
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov

local notation "eL" => LeanLab.PNTPort.LargeSieve.e

/-- Cauchy-Schwarz against `1` on `[-ξ, ξ]`, by AM-GM. -/
lemma integral_norm_le_sqrt_sym {g : ℝ → ℂ} (hg : Continuous g) {ξ B : ℝ} (hξ : 0 < ξ) (hB0 : 0 < B)
    (hB : ∫ α in (-ξ)..ξ, ‖g α‖ ^ 2 ≤ B) :
    ∫ α in (-ξ)..ξ, ‖g α‖ ≤ Real.sqrt (2 * ξ * B) := by
  have hle : -ξ ≤ ξ := by linarith
  set s := Real.sqrt (B / (2 * ξ)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = B / (2 * ξ) := Real.sq_sqrt (by positivity)
  have hpt : ∀ α ∈ Set.Icc (-ξ) ξ, ‖g α‖ ≤ (1 / (2 * s)) * ‖g α‖ ^ 2 + s / 2 := by
    intro α _
    have h := sq_nonneg (‖g α‖ - s)
    have e : (1 / (2 * s)) * ‖g α‖ ^ 2 + s / 2 = (‖g α‖ ^ 2 + s ^ 2) / (2 * s) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith
  have hc : Continuous (fun α => (1 / (2 * s)) * ‖g α‖ ^ 2 + s / 2) :=
    (continuous_const.mul (hg.norm.pow 2)).add continuous_const
  have hm := intervalIntegral.integral_mono_on (μ := volume) hle
    (hg.norm.intervalIntegrable _ _) (hc.intervalIntegrable _ _) hpt
  have hR : ∫ α in (-ξ)..ξ, ((1 / (2 * s)) * ‖g α‖ ^ 2 + s / 2)
      = (1 / (2 * s)) * (∫ α in (-ξ)..ξ, ‖g α‖ ^ 2) + (ξ - -ξ) * (s / 2) := by
    rw [intervalIntegral.integral_add (f := fun α => (1 / (2 * s)) * ‖g α‖ ^ 2) (g := fun _ => s / 2)
      ((continuous_const.mul (hg.norm.pow 2)).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
  rw [hR] at hm
  refine hm.trans ?_
  have h1 := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 1 / (2 * s))
  have e : 1 / (2 * s) * B + (ξ - -ξ) * (s / 2) = Real.sqrt (2 * ξ * B) := by
    have hsq : Real.sqrt (2 * ξ * B) = 2 * ξ * s := by
      rw [hs, show 2 * ξ * B = (2 * ξ) ^ 2 * (B / (2 * ξ)) by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [hsq]
    have hB' : B = 2 * ξ * s ^ 2 := by rw [hs2]; field_simp
    rw [hB']; field_simp; ring
  linarith

set_option maxHeartbeats 4000000 in
/-- **`I₃` at `y = H`, eq. (30), under RH, every `H ≤ N`.** -/
theorem I3_bound_full (hRH : RiemannHypothesis) : ∃ K₁ : ℝ, 0 ≤ K₁ ∧
    ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N →
      ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - 1 / zz N α) ^ 2‖
        ≤ 48 * K₁ * H * N * (1 + Real.log (2 * N / H)) ^ 2 := by
  obtain ⟨K₁, hK₁, hl1⟩ := lemma1_full hRH
  refine ⟨K₁, hK₁, fun N H hN hH hHNn => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNn : 1 ≤ N := by omega
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hHN : (H : ℝ) ≤ N := by exact_mod_cast hHNn
  set f : ℝ → ℝ := fun α => ‖St N α - 1 / zz N α‖ ^ 2 with hf
  have hfc : Continuous f := continuous_St_sub hNn
  have hTc := continuous_TH_neg N H
  have hK : (H : ℝ) ≤ 2 ^ H := by
    have := Nat.lt_two_pow_self (n := H); exact_mod_cast this.le
  -- step 1: `‖∫ T R̃²‖ ≤ ∫ ‖T(−α)‖ f`
  have h1 : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - 1 / zz N α) ^ 2‖
      ≤ ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖TH N H H (-α)‖ * f α := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans (le_of_eq ?_)
    congr 1; ext α; rw [norm_mul, norm_pow]
  -- step 2: the layer bound
  have h2 := integral_G_sq_le (H := H) (K := H) hH hK hfc (fun α => by positivity) hTc.norm
    (fun α hα => by
      have hab : |α| ≤ 1 / 2 := abs_le.mpr ⟨hα.1, hα.2⟩
      rw [← G_neg hab]; exact lemma5_full hHNn (-α))
  -- step 3: Lemma 1 on each window
  set a := Real.log (2 * N / H) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (by rw [le_div_iff₀ hH0]; linarith)
  have hlo : 1 / (2 * (N : ℝ)) ≤ 1 / (2 * H) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hwin : ∀ k ∈ range (H + 1), 4 * (H : ℝ) ^ 2 / 4 ^ k * ∫ α in (-xi H k)..(xi H k), f α
      ≤ 4 * K₁ * H * N * (1 + a) ^ 2 * (((k : ℝ) + 1) ^ 2 / 2 ^ k) := by
    intro k _
    have hx0 : 1 / (2 * H) ≤ xi H k := by
      unfold xi
      apply le_min
      · rw [div_le_div_iff₀ (by positivity) hH0]
        have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith
      · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hl := hl1 N hNn (xi H k) (hlo.trans hx0) (xi_le_half H k)
    have hxi0 : 0 < xi H k := lt_of_lt_of_le (by positivity) hx0
    have hxle := xi_le H k
    -- the log
    have h2N : 1 ≤ 2 * N * xi H k := by
      have : 2 * (N : ℝ) * (1 / (2 * H)) ≤ 2 * N * xi H k :=
        mul_le_mul_of_nonneg_left hx0 (by positivity)
      have e : 2 * (N : ℝ) * (1 / (2 * H)) = N / H := by field_simp
      rw [e] at this
      have : (1 : ℝ) ≤ N / H := by rw [le_div_iff₀ hH0]; linarith
      linarith
    have hlg0 : 0 ≤ Real.log (2 * N * xi H k) := Real.log_nonneg h2N
    have hlg : Real.log (2 * N * xi H k) ≤ a + k := by
      have h1 : 2 * N * xi H k ≤ (2 * N / H) * 2 ^ k := by
        have := mul_le_mul_of_nonneg_left hxle (show (0 : ℝ) ≤ 2 * N by positivity)
        calc 2 * N * xi H k ≤ 2 * N * ((2 : ℝ) ^ k / H) := this
          _ = (2 * N / H) * 2 ^ k := by ring
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_mul (x := 2 * N / H) (y := 2 ^ k) (by positivity) (by positivity), Real.log_pow] at h2
      have : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have : (k : ℝ) * Real.log 2 ≤ k := by nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
      linarith
    have hsq : (1 + Real.log (2 * N * xi H k)) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 * (1 + a) ^ 2 := by
      have : 1 + Real.log (2 * N * xi H k) ≤ ((k : ℝ) + 1) * (1 + a) := by
        nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) this 2
    have hint : ∫ α in (-xi H k)..(xi H k), f α
        ≤ K₁ * N * ((2 : ℝ) ^ k / H) * (((k : ℝ) + 1) ^ 2 * (1 + a) ^ 2) := by
      refine hl.trans ?_
      have := mul_le_mul hxle hsq (by positivity) (by positivity)
      calc K₁ * N * xi H k * (1 + Real.log (2 * N * xi H k)) ^ 2
          = K₁ * N * (xi H k * (1 + Real.log (2 * N * xi H k)) ^ 2) := by ring
        _ ≤ K₁ * N * ((2 : ℝ) ^ k / H * (((k : ℝ) + 1) ^ 2 * (1 + a) ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
    calc 4 * (H : ℝ) ^ 2 / 4 ^ k * ∫ α in (-xi H k)..(xi H k), f α
        ≤ 4 * (H : ℝ) ^ 2 / 4 ^ k * (K₁ * N * ((2 : ℝ) ^ k / H) * (((k : ℝ) + 1) ^ 2 * (1 + a) ^ 2)) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = 4 * K₁ * H * N * (1 + a) ^ 2 * (((k : ℝ) + 1) ^ 2 / 2 ^ k) := by
          rw [h4]; field_simp
  have h3 := sum_le_sum hwin
  rw [← mul_sum] at h3
  have h12 := sum_sq_div_two_pow_le (H + 1)
  have : 4 * K₁ * H * N * (1 + a) ^ 2 * ∑ k ∈ range (H + 1), ((k : ℝ) + 1) ^ 2 / 2 ^ k
      ≤ 4 * K₁ * H * N * (1 + a) ^ 2 * 12 := mul_le_mul_of_nonneg_left h12 (by positivity)
  linarith


set_option maxHeartbeats 4000000 in
/-- **`I₂` at `y = H`, with Lemma 1 on dyadic layers, under RH.** -/
theorem I2_bound_fine (hRH : RiemannHypothesis) : ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ N H : ℕ, (10 : ℝ) ^ 20 ≤ N → 1 ≤ H → H ≤ N →
    ‖2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      - 2 * ∑ n ∈ Icc (N - H) (N + H), ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)‖
      ≤ 2 * (K₂ * H * Real.sqrt N * (1 + Real.log (2 * N / H)) + 8 * Real.sqrt ((H : ℝ) ^ 3 * (1 + N / 2))
        + (H : ℝ) ^ 2) := by
  obtain ⟨K₁, hK₁, hl1⟩ := lemma1_full hRH
  refine ⟨384 * Real.sqrt (2 * (K₁ + 1)), by positivity, fun N H hN hH hHN => ?_⟩
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set T : ℝ → ℂ := fun α => TH N H H (-α) with hT
  set Rt : ℝ → ℂ := fun α => St N α - 1 / zz N α with hRt
  set iz : ℝ → ℂ := fun α => 1 / zz N α with hiz
  have hTc : Continuous T := continuous_TH_neg N H
  have hStc : Continuous (St N) := continuous_St hNn
  have hizc : Continuous iz := continuous_const.div (continuous_zz N) (zz_ne_zero hNn)
  have hWc : Continuous (Wz N) := continuous_Wz hNn
  have hRtc : Continuous Rt := hStc.sub hizc
  -- the split
  have hsplit : ∀ α, T α * Rt α * iz α = T α * Rt α * (iz α - Wz N α)
      + T α * (Wz N α - iz α) * Wz N α + T α * (St N α - Wz N α) * Wz N α := by
    intro α; simp only [hRt, hiz]; ring
  have i1 : IntervalIntegrable (fun α => T α * Rt α * (iz α - Wz N α)) volume (-(1 / 2 : ℝ)) (1 / 2) :=
    ((hTc.mul hRtc).mul (hizc.sub hWc)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun α => T α * (Wz N α - iz α) * Wz N α) volume (-(1 / 2 : ℝ)) (1 / 2) :=
    ((hTc.mul (hWc.sub hizc)).mul hWc).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun α => T α * (St N α - Wz N α) * Wz N α) volume
      (-(1 / 2 : ℝ)) (1 / 2) :=
    ((hTc.mul (hStc.sub hWc)).mul hWc).intervalIntegrable _ _
  have hint : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α
      = (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α))
        + (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α)
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α := by
    simp_rw [hsplit]
    rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2]
  have hDW := DW_eq (H := H) hNn
  -- pointwise bounds on `[-1/2, 1/2]`
  have hgeom : ∀ α ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ‖iz α - Wz N α‖ ≤ 8 := by
    intro α hα
    have hre : (zz N α).re = 1 / N := by simp [zz]
    have him : (zz N α).im = -(2 * Real.pi * α) := by simp [zz]
    have hb := LeanLab.PNTPort.Selberg.geom_sub_inv_le (z := zz N α) (by rw [hre]; positivity)
      (by rw [hre, div_le_one hN0]; exact hN1)
      (by rw [him, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          have : |α| ≤ 1 / 2 := abs_le.mpr ⟨hα.1, hα.2⟩
          nlinarith [Real.pi_pos])
    rw [norm_sub_rev]; exact hb
  have hTb : ∀ α, ‖T α‖ ≤ (H : ℝ) ^ 2 := fun α => norm_TH_le hHN _
  -- `∫ ‖Rt‖ ≤ √(4 N log N)`
  have hlog46 : (46 : ℝ) ≤ Real.log N := le_trans LeanLab.Zinoviev1997.log_1e20_ge
    (Real.log_le_log (by norm_num) hN)
  have hR2 : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖Rt α‖ ^ 2 ≤ 4 * N * Real.log N := by
    have := lemma3_upper N hN
    have : (N : ℝ) + 130 ≤ 2 * N * Real.log N := by nlinarith
    linarith
  have hR1 := integral_norm_le_sqrt hRtc (by positivity) hR2
  -- `∫ ‖W‖ ≤ √(1 + N/2)`
  have hW2 : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖Wz N α‖ ^ 2 ≤ 1 + N / 2 := by
    have : (fun α => ‖Wz N α‖ ^ 2) = fun α => ‖∑' m, wc N m * eL (m * α)‖ ^ 2 :=
      funext fun α => by rw [W_eq hNn]
    rw [this, parseval_tsum _ (summable_wc hNn)]
    exact tsum_exp_two_le hNn
  have hW1 := integral_norm_le_sqrt hWc (by positivity) hW2
  -- the three pieces
  have hT2 : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖T α‖ ^ 2 ≤ (H : ℝ) ^ 3 := TH_L2 (y := (H : ℝ)) hHN
  set a := Real.log (2 * N / H) with ha
  have hHr : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have ha0 : 0 ≤ a := Real.log_nonneg (by rw [le_div_iff₀ hH0]; linarith)
  set c := Real.sqrt (2 * (K₁ + 1)) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have b1 : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α)‖
      ≤ 384 * c * H * Real.sqrt N * (1 + a) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans ?_
    have m1 : IntervalIntegrable (fun α => ‖T α * Rt α * (iz α - Wz N α)‖) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      ((hTc.mul hRtc).mul (hizc.sub hWc)).norm.intervalIntegrable _ _
    have m2 : IntervalIntegrable (fun α => ‖T α‖ * (8 * ‖Rt α‖)) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (hTc.norm.mul (continuous_const.mul hRtc.norm)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)
      m1 m2
      (fun α hα => show ‖T α * Rt α * (iz α - Wz N α)‖ ≤ ‖T α‖ * (8 * ‖Rt α‖) by
        rw [norm_mul, norm_mul]
        have := hgeom α hα
        nlinarith [norm_nonneg (Rt α), norm_nonneg (T α), mul_nonneg (norm_nonneg (T α)) (norm_nonneg (Rt α))])
    refine hm.trans ?_
    have hK : (H : ℝ) ≤ 2 ^ H := by
      have := Nat.lt_two_pow_self (n := H); exact_mod_cast this.le
    have hlay := integral_G_sq_le (H := H) (K := H) (f := fun α => 8 * ‖Rt α‖) hH hK (continuous_const.mul hRtc.norm)
      (fun α => mul_nonneg (by norm_num) (norm_nonneg _)) hTc.norm
      (fun α hα => by
        have hab : |α| ≤ 1 / 2 := abs_le.mpr ⟨hα.1, hα.2⟩
        show ‖TH N H H (-α)‖ ≤ G H α ^ 2
        rw [← G_neg hab]; exact lemma5_full hHN (-α))
    refine hlay.trans ?_
    have hwin : ∀ k ∈ range (H + 1), 4 * (H : ℝ) ^ 2 / 4 ^ k * ∫ α in (-xi H k)..(xi H k), 8 * ‖Rt α‖
        ≤ 32 * c * H * Real.sqrt N * (1 + a) * (((k : ℝ) + 1) ^ 2 / 2 ^ k) := by
      intro k _
      have hx0 : 1 / (2 * H) ≤ xi H k := by
        unfold xi
        apply le_min
        · rw [div_le_div_iff₀ (by positivity) hH0]
          have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
          nlinarith
        · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have hlo : 1 / (2 * (N : ℝ)) ≤ 1 / (2 * H) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have hl := hl1 N hNn (xi H k) (hlo.trans hx0) (xi_le_half H k)
      have hxi0 : 0 < xi H k := lt_of_lt_of_le (by positivity) hx0
      have hxle := xi_le H k
      have h2N : 1 ≤ 2 * N * xi H k := by
        have : 2 * (N : ℝ) * (1 / (2 * H)) ≤ 2 * N * xi H k :=
          mul_le_mul_of_nonneg_left hx0 (by positivity)
        have e : 2 * (N : ℝ) * (1 / (2 * H)) = N / H := by field_simp
        rw [e] at this
        have : (1 : ℝ) ≤ N / H := by rw [le_div_iff₀ hH0]; linarith
        linarith
      have hlg0 : 0 ≤ Real.log (2 * N * xi H k) := Real.log_nonneg h2N
      have hlg : Real.log (2 * N * xi H k) ≤ a + k := by
        have h1 : 2 * N * xi H k ≤ (2 * N / H) * 2 ^ k := by
          have := mul_le_mul_of_nonneg_left hxle (show (0 : ℝ) ≤ 2 * N by positivity)
          calc 2 * N * xi H k ≤ 2 * N * ((2 : ℝ) ^ k / H) := this
            _ = (2 * N / H) * 2 ^ k := by ring
        have h2 := Real.log_le_log (by positivity) h1
        rw [Real.log_mul (x := 2 * N / H) (y := 2 ^ k) (by positivity) (by positivity), Real.log_pow] at h2
        have : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
        have : (k : ℝ) * Real.log 2 ≤ k := by nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
        linarith
      set ℓ := Real.log (2 * N * xi H k) with hℓ
      have hone : 1 + ℓ ≤ ((k : ℝ) + 1) * (1 + a) := by
        nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
      -- `∫ ‖Rt‖ ≤ ξ (1 + ℓ) √(2 (K₁ + 1) N)`
      have hB : ∫ α in (-xi H k)..(xi H k), ‖Rt α‖ ^ 2 ≤ (K₁ + 1) * N * xi H k * (1 + ℓ) ^ 2 := by
        refine hl.trans ?_
        have : 0 ≤ N * xi H k * (1 + ℓ) ^ 2 := by positivity
        nlinarith
      have hR := integral_norm_le_sqrt_sym hRtc hxi0 (by positivity) hB
      have hsq : Real.sqrt (2 * xi H k * ((K₁ + 1) * N * xi H k * (1 + ℓ) ^ 2))
          = xi H k * (1 + ℓ) * (c * Real.sqrt N) := by
        rw [hc, ← Real.sqrt_mul (by positivity)]
        rw [show 2 * xi H k * ((K₁ + 1) * N * xi H k * (1 + ℓ) ^ 2)
          = (xi H k * (1 + ℓ)) ^ 2 * (2 * (K₁ + 1) * N) by ring]
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      rw [hsq] at hR
      rw [intervalIntegral.integral_const_mul]
      have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
      have hxk : xi H k * (1 + ℓ) ≤ (2 : ℝ) ^ k / H * (((k : ℝ) + 1) * (1 + a)) :=
        mul_le_mul hxle hone (by linarith) (by positivity)
      have hRk : ∫ α in (-xi H k)..(xi H k), ‖Rt α‖
          ≤ (2 : ℝ) ^ k / H * (((k : ℝ) + 1) * (1 + a)) * (c * Real.sqrt N) :=
        hR.trans (mul_le_mul_of_nonneg_right hxk (by positivity))
      calc 4 * (H : ℝ) ^ 2 / 4 ^ k * (8 * ∫ α in (-xi H k)..(xi H k), ‖Rt α‖)
          ≤ 4 * (H : ℝ) ^ 2 / 4 ^ k * (8 * ((2 : ℝ) ^ k / H * (((k : ℝ) + 1) * (1 + a)) * (c * Real.sqrt N))) := by
            gcongr
        _ = 32 * c * H * Real.sqrt N * (1 + a) * (((k : ℝ) + 1) / 2 ^ k) := by
            rw [h4]; field_simp; ring
        _ ≤ 32 * c * H * Real.sqrt N * (1 + a) * (((k : ℝ) + 1) ^ 2 / 2 ^ k) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply div_le_div_of_nonneg_right _ (by positivity)
            nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
    have h3 := sum_le_sum hwin
    rw [← mul_sum] at h3
    have h12 := sum_sq_div_two_pow_le (H + 1)
    have : 32 * c * H * Real.sqrt N * (1 + a) * ∑ k ∈ range (H + 1), ((k : ℝ) + 1) ^ 2 / 2 ^ k
        ≤ 32 * c * H * Real.sqrt N * (1 + a) * 12 := mul_le_mul_of_nonneg_left h12 (by positivity)
    linarith
  have b2 : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α‖
      ≤ 8 * Real.sqrt ((H : ℝ) ^ 3 * (1 + N / 2)) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans ?_
    have m1 : IntervalIntegrable (fun α => ‖T α * (Wz N α - iz α) * Wz N α‖) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      ((hTc.mul (hWc.sub hizc)).mul hWc).norm.intervalIntegrable _ _
    have m2 : IntervalIntegrable (fun α => 8 * (‖T α‖ * ‖Wz N α‖)) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (continuous_const.mul (hTc.norm.mul hWc.norm)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)
      m1 m2
      (fun α hα => show ‖T α * (Wz N α - iz α) * Wz N α‖ ≤ 8 * (‖T α‖ * ‖Wz N α‖) by
        rw [norm_mul, norm_mul, norm_sub_rev]
        have := hgeom α hα
        nlinarith [norm_nonneg (Wz N α), norm_nonneg (T α), mul_nonneg (norm_nonneg (T α)) (norm_nonneg (Wz N α))])
    rw [intervalIntegral.integral_const_mul] at hm
    have := integral_norm_mul_le_sqrt hTc hWc (by positivity) (by positivity) hT2 hW2
    linarith
  have b3 : ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
      - ∑ n ∈ Icc (N - H) (N + H), ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)‖
      ≤ (H : ℝ) ^ 2 := by
    rw [show (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
      = ∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - Wz N α) * Wz N α from rfl, hDW,
      ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    rw [← sum_tw hHN]
    refine sum_le_sum fun n hn => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have e : tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n - 1))
        - tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) = -(tw N H n * Real.exp (-(n / N))) := by
      ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg (tw_nonneg hHN hn) (Real.exp_pos _).le)]
    have : Real.exp (-(n / N)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0 : ℝ) ≤ n / N := by positivity
      linarith
    nlinarith [tw_nonneg hHN hn]
  -- assembly
  have hgoal : (2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      - 2 * ∑ n ∈ Icc (N - H) (N + H), ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))
      = 2 * ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α))
        + (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α)
        + ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
          - ∑ n ∈ Icc (N - H) (N + H),
            ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))) := by
    rw [show (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      = ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α from rfl, hint]
    ring
  rw [hgoal, norm_mul, Complex.norm_ofNat]
  have := norm_add₃_le (a := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α))
      (b := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α)
      (c := (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
      - ∑ n ∈ Icc (N - H) (N + H), ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))
  nlinarith


set_option maxHeartbeats 4000000 in
/-- **P0058 Theorem 2 eq. (3), as printed, under RH, for every `1 ≤ H ≤ N`.** -/
theorem theorem2b_full (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ N H : ℕ, (10 : ℝ) ^ 20 ≤ N → 1 ≤ H → H ≤ N →
      |wsum N H H| ≤ K * N * Real.log (2 * N / H) ^ 2 := by
  obtain ⟨K₁, hK₁, hI3⟩ := I3_bound_full hRH
  obtain ⟨K₂, hK₂, hI2⟩ := I2_bound_fine hRH
  refine ⟨80 + 18 * K₂ + 432 * K₁, by positivity, fun N H hN hH hHNn => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  have hN2n : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := le_trans (by norm_num) hN
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by linarith
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hsle : Real.sqrt (N : ℝ) ≤ N := by nlinarith
  have hHN : (H : ℝ) ≤ N := by exact_mod_cast hHNn
  -- the pieces
  set T : ℝ → ℂ := fun α => TH N H H (-α)
  set Rt : ℝ → ℂ := fun α => St N α - 1 / zz N α
  set iz : ℝ → ℂ := fun α => 1 / zz N α
  have hTc : Continuous T := continuous_TH_neg N H
  have hStc : Continuous (St N) := continuous_St hNn
  have hizc : Continuous iz := continuous_const.div (continuous_zz N) (zz_ne_zero hNn)
  have hRtc : Continuous Rt := hStc.sub hizc
  have hpt : ∀ α, St N α ^ 2 * TH N H H (-α)
      = T α * iz α ^ 2 + 2 * (T α * Rt α * iz α) + T α * Rt α ^ 2 := by
    intro α; simp only [T, Rt, iz]; ring
  have hQ := Q_eq (H := H) hNn
  have hdec : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), St N α ^ 2 * TH N H H (-α)
      = (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2)
        + 2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α)
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2 := by
    simp_rw [hpt]
    have j1 : IntervalIntegrable (fun α => T α * iz α ^ 2) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (hTc.mul (hizc.pow 2)).intervalIntegrable _ _
    have j2 : IntervalIntegrable (fun α => 2 * (T α * Rt α * iz α)) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (continuous_const.mul ((hTc.mul hRtc).mul hizc)).intervalIntegrable _ _
    have j3 : IntervalIntegrable (fun α => T α * Rt α ^ 2) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (hTc.mul (hRtc.pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (j1.add j2) j3, intervalIntegral.integral_add j1 j2,
      intervalIntegral.integral_const_mul]
  have b1 := I1_bound_le hNn hHNn
  have b2 := hI2 N H hN hH hHNn
  have b3 := hI3 N H hN2n hH hHNn
  -- the real identity
  set M1 : ℝ := ∑ n ∈ Icc (N - H) (N + H), tw N H n * (n * Real.exp (-n / N))
  set M2 : ℝ := ∑ n ∈ Icc (N - H) (N + H), tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n))
  set Qr : ℝ := ∑ n ∈ Icc (N - H) (N + H), tw N H n * Real.exp (-n / N) * R n
  have hw : (H : ℝ) * wsum N H H = Qr - M1 - 2 * M2 := by
    have hfilt : (Icc (N - H) (N + H)).filter (fun n : ℕ => (n : ℝ) ≤ N + H) = Icc (N - H) (N + H) := by
      apply filter_true_of_mem; intro n hn; rw [mem_Icc] at hn; exact_mod_cast hn.2
    unfold wsum
    rw [hfilt, mul_sum]
    simp only [Qr, M1, M2, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [w_eq hH]
    unfold tw
    rw [neg_div]
    field_simp
    ring
  have hwC : (((H : ℝ) * wsum N H H : ℝ) : ℂ)
      = ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ))
        + (2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ))
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2 := by
    have : ((Qr : ℝ) : ℂ) = (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2)
        + 2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α)
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2 := by
      rw [← hdec, hQ]; simp only [Qr]; push_cast; rfl
    rw [hw]; push_cast; rw [this]; ring
  have hM1 : ((M1 : ℝ) : ℂ) = ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ) := by simp only [M1]; push_cast; rfl
  have hM2 : ((M2 : ℝ) : ℂ) = ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ) := by
    simp only [M2]; push_cast; rfl
  have hA : ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ)‖ ≤ (H : ℝ) ^ 2 := by
    rw [hM1]; exact b1
  have hB : ‖2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ)‖
      ≤ 2 * (K₂ * H * Real.sqrt N * (1 + Real.log (2 * N / H)) + 8 * Real.sqrt ((H : ℝ) ^ 3 * (1 + N / 2))
        + (H : ℝ) ^ 2) := by
    rw [hM2]; exact b2
  have hC : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2‖
      ≤ 48 * K₁ * H * N * (1 + Real.log (2 * N / H)) ^ 2 := b3
  have htot : (H : ℝ) * |wsum N H H| ≤ (H : ℝ) ^ 2
      + 2 * (K₂ * H * Real.sqrt N * (1 + Real.log (2 * N / H)) + 8 * Real.sqrt ((H : ℝ) ^ 3 * (1 + N / 2))
        + (H : ℝ) ^ 2)
      + 48 * K₁ * H * N * (1 + Real.log (2 * N / H)) ^ 2 := by
    have h := norm_add₃_le (a := (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ))
      (b := 2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ))
      (c := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2)
    rw [← hwC, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hH0] at h
    linarith
  -- divide by `H`
  have hs2 : Real.sqrt ((H : ℝ) ^ 3 * (1 + N / 2)) ≤ H * N := by
    rw [show (H : ℝ) * N = Real.sqrt ((H * N) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have h1 : (H : ℝ) * (1 + N / 2) ≤ (N : ℝ) ^ 2 := by nlinarith
    have e : ((H : ℝ) * N) ^ 2 = (H : ℝ) ^ 2 * (N : ℝ) ^ 2 := by ring
    rw [e, show (H : ℝ) ^ 3 * (1 + N / 2) = (H : ℝ) ^ 2 * (H * (1 + N / 2)) by ring]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  set a := Real.log (2 * N / H) with ha
  have ha2 : Real.log 2 ≤ a := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hH0]; linarith
  have hl2 := Real.log_two_gt_d9
  have ha0 : 0 ≤ a := by linarith
  have hdiv : |wsum N H H| ≤ 3 * H + 2 * K₂ * Real.sqrt N * (1 + a) + 16 * N + 48 * K₁ * N * (1 + a) ^ 2 := by
    have h : (H : ℝ) * |wsum N H H| ≤
        H * (3 * H + 2 * K₂ * Real.sqrt N * (1 + a) + 16 * N + 48 * K₁ * N * (1 + a) ^ 2) := by
      refine htot.trans ?_
      nlinarith
    exact le_of_mul_le_mul_left h hH0
  have hfin : 3 * (H : ℝ) + 2 * K₂ * Real.sqrt N * (1 + a) + 16 * N + 48 * K₁ * N * (1 + a) ^ 2
      ≤ (80 + 18 * K₂ + 432 * K₁) * N * a ^ 2 := by
    have h1 : (1 + a) ^ 2 ≤ 9 * a ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ 4 * a ^ 2 := by nlinarith
    have h1a : 1 + a ≤ (1 + a) ^ 2 := by nlinarith
    have hq : Real.sqrt N * (1 + a) ≤ N * (1 + a) ^ 2 :=
      mul_le_mul hsle h1a (by linarith) (by positivity)
    have h3 : 48 * K₁ * N * (1 + a) ^ 2 ≤ 432 * K₁ * N * a ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 48 * K₁ * N by positivity); nlinarith
    have h3' : 2 * K₂ * Real.sqrt N * (1 + a) ≤ 18 * K₂ * N * a ^ 2 := by
      have := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 2 * K₂ by positivity)
      have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * K₂ * N by positivity)
      nlinarith
    have h4 : 3 * (H : ℝ) + 16 * N ≤ 19 * N := by linarith
    have h5 : 19 * (N : ℝ) ≤ 80 * N * a ^ 2 := by nlinarith
    nlinarith
  linarith

end LeanLab.LZCesaroShort
