import LeanLab.LZCesaroShort.Lemma1Proved
import LeanLab.LZCesaroShort.I1Le

/-!
# P0058 Theorem 2 eq. (2) from RH for every `1 ≤ H ≤ N`

Lab proof, unit U-6202, CLOUD 20261020T0817Z-cloud38, T1. AI wrote this file. CONDITIONAL ON
RiemannHypothesis only. Binary Goldbach is OPEN.

`theorem2a_short` needed `2H(log N + 1) ≤ √N` twice: for Lemma 1 at small `ξ`, now
`I3_boundY_full`, and in `I2_boundY`, which bounds `T_H` by its sup `H²`. Here
* `TH_L2`: `∫ ‖T_H(N, y; −α)‖² ≤ H³`, by Parseval;
* `integral_norm_mul_le_sqrt`: Cauchy-Schwarz on `[−1/2, 1/2]`;
* `I2_boundY_full`: `I₂` with error `2(8√(H³ · 4N log N) + 8√(H³(1 + N/2)) + H²)`;
* `theorem2a_full`: **under RH**, for `N ≥ 10^20`, `1 ≤ H ≤ N` and `y ∈ [−H, H)`,
  `|wsum N H y| ≤ K N log² N log(2H)`, P0058 Theorem 2 eq. (2) on the paper's whole range.
-/

namespace LeanLab.LZCesaroShort
open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Chebyshev
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher
local notation "eL" => LeanLab.PNTPort.LargeSieve.e

lemma tw_le {N H n : ℕ} : tw N H n ≤ H := by
  unfold tw; linarith [abs_nonneg ((n : ℝ) - N)]

/-- `∫ ‖T_H(N, y; −α)‖² ≤ H³`, by Parseval. -/
lemma TH_L2 {N H : ℕ} {y : ℝ} (hHN : H ≤ N) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖TH N H y (-α)‖ ^ 2 ≤ (H : ℝ) ^ 3 := by
  have hneg : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖TH N H y (-α)‖ ^ 2
      = ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖TH N H y α‖ ^ 2 := by
    rw [intervalIntegral.integral_comp_neg (fun α => ‖TH N H y α‖ ^ 2), neg_neg]
  rw [hneg]
  set M := N + H + 1 with hM
  set b : ℕ → ℂ := fun m => if m ∈ Fy N H y then ((tw N H m : ℝ) : ℂ) else 0 with hb
  have hsub : Fy N H y ⊆ range M := by
    intro n hn
    have := (mem_filter.mp hn).1
    rw [mem_Icc] at this; rw [mem_range]; omega
  have hT : ∀ α, TH N H y α = ∑ m ∈ range M, b m * eL (m * α) := by
    intro α
    rw [TH_eqY]
    rw [← sum_subset hsub (fun m _ hm => by simp [hb, hm])]
    refine sum_congr rfl fun m hm => ?_
    simp [hb, hm]
  simp_rw [hT]
  rw [parseval b M]
  rw [← sum_subset hsub (fun m _ hm => by simp [hb, hm])]
  have : ∀ m ∈ Fy N H y, ‖b m‖ ^ 2 ≤ H * tw N H m := by
    intro m hm
    simp only [hb, hm, if_true, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h0 := tw_nonnegY hHN hm
    nlinarith [tw_le (N := N) (H := H) (n := m)]
  refine (sum_le_sum this).trans ?_
  rw [← mul_sum]
  have := sum_twY_le (y := y) hHN
  have h0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  calc (H : ℝ) * ∑ i ∈ Fy N H y, tw N H i ≤ H * (H : ℝ) ^ 2 := mul_le_mul_of_nonneg_left this h0
    _ = (H : ℝ) ^ 3 := by ring

/-- Cauchy-Schwarz on `[-1/2, 1/2]`, by AM-GM. -/
lemma integral_norm_mul_le_sqrt {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hfa : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖f α‖ ^ 2 ≤ a)
    (hgb : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖g α‖ ^ 2 ≤ b) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖f α‖ * ‖g α‖ ≤ Real.sqrt (a * b) := by
  set sa := Real.sqrt a with hsa
  set sb := Real.sqrt b with hsb
  have hsa0 : 0 < sa := Real.sqrt_pos.mpr ha
  have hsb0 : 0 < sb := Real.sqrt_pos.mpr hb
  have hsa2 : sa ^ 2 = a := Real.sq_sqrt ha.le
  have hsb2 : sb ^ 2 = b := Real.sq_sqrt hb.le
  set t := sb / sa with ht
  have ht0 : 0 < t := div_pos hsb0 hsa0
  have hpt : ∀ α ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
      ‖f α‖ * ‖g α‖ ≤ t / 2 * ‖f α‖ ^ 2 + 1 / (2 * t) * ‖g α‖ ^ 2 := by
    intro α _
    have h := sq_nonneg (t * ‖f α‖ - ‖g α‖)
    have e : t / 2 * ‖f α‖ ^ 2 + 1 / (2 * t) * ‖g α‖ ^ 2
        = ((t * ‖f α‖) ^ 2 + ‖g α‖ ^ 2) / (2 * t) := by field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith
  have hc : Continuous (fun α => t / 2 * ‖f α‖ ^ 2 + 1 / (2 * t) * ‖g α‖ ^ 2) :=
    (continuous_const.mul (hf.norm.pow 2)).add (continuous_const.mul (hg.norm.pow 2))
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)
    ((hf.norm.mul hg.norm).intervalIntegrable _ _) (hc.intervalIntegrable _ _) hpt
  have hR : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), (t / 2 * ‖f α‖ ^ 2 + 1 / (2 * t) * ‖g α‖ ^ 2)
      = t / 2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖f α‖ ^ 2)
        + 1 / (2 * t) * ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖g α‖ ^ 2 := by
    rw [intervalIntegral.integral_add (f := fun α => t / 2 * ‖f α‖ ^ 2)
      (g := fun α => 1 / (2 * t) * ‖g α‖ ^ 2)
      ((continuous_const.mul (hf.norm.pow 2)).intervalIntegrable _ _)
      ((continuous_const.mul (hg.norm.pow 2)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hR] at hm
  refine hm.trans ?_
  have h1 := mul_le_mul_of_nonneg_left hfa (by positivity : (0 : ℝ) ≤ t / 2)
  have h2 := mul_le_mul_of_nonneg_left hgb (by positivity : (0 : ℝ) ≤ 1 / (2 * t))
  have e : t / 2 * a + 1 / (2 * t) * b = Real.sqrt (a * b) := by
    rw [Real.sqrt_mul ha.le, ← hsa, ← hsb, ht, ← hsa2, ← hsb2]
    field_simp; ring
  linarith


/-- **`I₂` with `‖T‖₂ ≤ H^{3/2}` in place of `‖T‖∞ ≤ H²`.** -/
theorem I2_boundY_full {N H : ℕ} {y : ℝ} (hN : (10 : ℝ) ^ 20 ≤ N) (hHN : H ≤ N) :
    ‖2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      - 2 * ∑ n ∈ Fy N H y, ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)‖
      ≤ 2 * (8 * Real.sqrt ((H : ℝ) ^ 3 * (4 * N * Real.log N)) + 8 * Real.sqrt ((H : ℝ) ^ 3 * (1 + N / 2))
        + (H : ℝ) ^ 2) := by
  have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set T : ℝ → ℂ := fun α => TH N H y (-α) with hT
  set Rt : ℝ → ℂ := fun α => St N α - 1 / zz N α with hRt
  set iz : ℝ → ℂ := fun α => 1 / zz N α with hiz
  have hTc : Continuous T := continuous_THY_neg N H y
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
  have hDW := DW_eqY (H := H) (y := y) hNn
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
  have hTb : ∀ α, ‖T α‖ ≤ (H : ℝ) ^ 2 := fun α => norm_THY_le hHN _
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
  have hT2 : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖T α‖ ^ 2 ≤ (H : ℝ) ^ 3 := TH_L2 hHN
  have hH3 : 0 < (H : ℝ) ^ 3 ∨ H = 0 := by
    rcases Nat.eq_zero_or_pos H with h | h
    · exact Or.inr h
    · exact Or.inl (by positivity)
  have hlogpos : 0 < 4 * (N : ℝ) * Real.log N := by
    have : (0 : ℝ) < Real.log N := by linarith
    positivity
  -- pointwise `‖T‖ ≤ H²` gives `T = 0` when `H = 0`; otherwise Cauchy-Schwarz
  have cs : ∀ {g : ℝ → ℂ}, Continuous g → ∀ {B : ℝ}, 0 < B →
      ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖g α‖ ^ 2 ≤ B →
      ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖T α‖ * ‖g α‖ ≤ Real.sqrt ((H : ℝ) ^ 3 * B) := by
    intro g hg B hB hgB
    rcases hH3 with h | h
    · exact integral_norm_mul_le_sqrt hTc hg h hB hT2 hgB
    · have hT0 : ∀ α, ‖T α‖ = 0 := fun α => by
        have := hTb α; rw [h] at this; simp at this; simp [this]
      simp_rw [hT0, zero_mul, intervalIntegral.integral_zero]
      exact Real.sqrt_nonneg _
  have b1 : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α)‖
      ≤ 8 * Real.sqrt ((H : ℝ) ^ 3 * (4 * N * Real.log N)) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans ?_
    have m1 : IntervalIntegrable (fun α => ‖T α * Rt α * (iz α - Wz N α)‖) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      ((hTc.mul hRtc).mul (hizc.sub hWc)).norm.intervalIntegrable _ _
    have m2 : IntervalIntegrable (fun α => 8 * (‖T α‖ * ‖Rt α‖)) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (continuous_const.mul (hTc.norm.mul hRtc.norm)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)
      m1 m2
      (fun α hα => show ‖T α * Rt α * (iz α - Wz N α)‖ ≤ 8 * (‖T α‖ * ‖Rt α‖) by
        rw [norm_mul, norm_mul]
        have := hgeom α hα
        nlinarith [norm_nonneg (Rt α), norm_nonneg (T α), mul_nonneg (norm_nonneg (T α)) (norm_nonneg (Rt α))])
    rw [intervalIntegral.integral_const_mul] at hm
    have := cs hRtc hlogpos hR2
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
    have := cs hWc (by positivity) hW2
    linarith
  have b3 : ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
      - ∑ n ∈ Fy N H y, ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)‖
      ≤ (H : ℝ) ^ 2 := by
    rw [show (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
      = ∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - Wz N α) * Wz N α from rfl, hDW,
      ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ (sum_twY_le (y := y) hHN)
    refine sum_le_sum fun n hn => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have e : tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n - 1))
        - tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) = -(tw N H n * Real.exp (-(n / N))) := by
      ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg (tw_nonnegY hHN hn) (Real.exp_pos _).le)]
    have : Real.exp (-(n / N)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0 : ℝ) ≤ n / N := by positivity
      linarith
    nlinarith [tw_nonnegY hHN hn]
  -- assembly
  have hgoal : (2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      - 2 * ∑ n ∈ Fy N H y, ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))
      = 2 * ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α))
        + (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α)
        + ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
          - ∑ n ∈ Fy N H y,
            ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))) := by
    rw [show (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      = ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α from rfl, hint]
    ring
  rw [hgoal, norm_mul, Complex.norm_ofNat]
  have := norm_add₃_le (a := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α))
      (b := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α)
      (c := (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
      - ∑ n ∈ Fy N H y, ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))
  nlinarith


set_option maxHeartbeats 4000000 in
/-- **P0058 Theorem 2 eq. (2) as printed, under RH, for every `1 ≤ H ≤ N`.** -/
theorem theorem2a_full (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ N H : ℕ, ∀ y : ℝ, (10 : ℝ) ^ 20 ≤ N → 1 ≤ H → H ≤ N →
      -(H : ℝ) ≤ y → y < H →
      |wsum N H y| ≤ K * N * Real.log N ^ 2 * Real.log (2 * H) := by
  obtain ⟨K₁, hK₁, hI3⟩ := I3_boundY_full hRH
  refine ⟨110 + 72 * K₁, by positivity, fun N H y hN hH hHNn hy0 hyH => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  have hN2n : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := le_trans (by norm_num) hN
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by linarith
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hHN : (H : ℝ) ≤ N := by exact_mod_cast hHNn
  -- the pieces
  set T : ℝ → ℂ := fun α => TH N H y (-α)
  set Rt : ℝ → ℂ := fun α => St N α - 1 / zz N α
  set iz : ℝ → ℂ := fun α => 1 / zz N α
  have hTc : Continuous T := continuous_THY_neg N H y
  have hStc : Continuous (St N) := continuous_St hNn
  have hizc : Continuous iz := continuous_const.div (continuous_zz N) (zz_ne_zero hNn)
  have hRtc : Continuous Rt := hStc.sub hizc
  have hpt : ∀ α, St N α ^ 2 * TH N H y (-α)
      = T α * iz α ^ 2 + 2 * (T α * Rt α * iz α) + T α * Rt α ^ 2 := by
    intro α; simp only [T, Rt, iz]; ring
  have hQ := Q_eqY (H := H) (y := y) hNn
  have hdec : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), St N α ^ 2 * TH N H y (-α)
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
  have b1 := I1_boundY_le (y := y) hNn hHNn
  have b2 := I2_boundY_full (y := y) hN hHNn
  have b3 := hI3 N H y hN2n hH hHNn hy0 hyH
  -- the real identity
  set M1 : ℝ := ∑ n ∈ Fy N H y, tw N H n * (n * Real.exp (-n / N))
  set M2 : ℝ := ∑ n ∈ Fy N H y, tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n))
  set Qr : ℝ := ∑ n ∈ Fy N H y, tw N H n * Real.exp (-n / N) * R n
  have hw : (H : ℝ) * wsum N H y = Qr - M1 - 2 * M2 := by
    unfold wsum
    rw [mul_sum]
    simp only [Qr, M1, M2, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [w_eq hH]
    unfold tw
    rw [neg_div]
    field_simp
    ring
  have hwC : (((H : ℝ) * wsum N H y : ℝ) : ℂ)
      = ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ))
        + (2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ))
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2 := by
    have : ((Qr : ℝ) : ℂ) = (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2)
        + 2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α)
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2 := by
      rw [← hdec, hQ]; simp only [Qr]; push_cast; rfl
    rw [hw]; push_cast; rw [this]; ring
  have hM1 : ((M1 : ℝ) : ℂ) = ∑ n ∈ Fy N H y,
      ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ) := by simp only [M1]; push_cast; rfl
  have hM2 : ((M2 : ℝ) : ℂ) = ∑ n ∈ Fy N H y,
      ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ) := by
    simp only [M2]; push_cast; rfl
  have hA : ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ)‖ ≤ (H : ℝ) ^ 2 := by
    rw [hM1]; exact b1
  have hB : ‖2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ)‖
      ≤ 2 * (8 * Real.sqrt ((H : ℝ) ^ 3 * (4 * N * Real.log N)) + 8 * Real.sqrt ((H : ℝ) ^ 3 * (1 + N / 2))
        + (H : ℝ) ^ 2) := by
    rw [hM2]; exact b2
  have hC : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2‖
      ≤ 18 * K₁ * H * N * (1 + Real.log N) ^ 2 * Real.log (2 * H) := b3
  have htot : (H : ℝ) * |wsum N H y| ≤ (H : ℝ) ^ 2
      + 2 * (8 * Real.sqrt ((H : ℝ) ^ 3 * (4 * N * Real.log N)) + 8 * Real.sqrt ((H : ℝ) ^ 3 * (1 + N / 2))
        + (H : ℝ) ^ 2)
      + 18 * K₁ * H * N * (1 + Real.log N) ^ 2 * Real.log (2 * H) := by
    have h := norm_add₃_le (a := (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ))
      (b := 2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ))
      (c := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2)
    rw [← hwC, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hH0] at h
    linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := le_trans (by norm_num) hN
    linarith
  have hl2 := Real.log_two_gt_d9
  have hlH : Real.log 2 ≤ Real.log (2 * H) := Real.log_le_log (by norm_num) (by linarith)
  set L := Real.log (2 * H)
  set lN := Real.log N with hlN
  have hNl : (N : ℝ) ≤ N * lN := by nlinarith
  have hs1 : Real.sqrt ((H : ℝ) ^ 3 * (4 * N * lN)) ≤ 2 * H * N * lN := by
    rw [show 2 * (H : ℝ) * N * lN = Real.sqrt ((2 * H * N * lN) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have : (H : ℝ) ≤ N * lN := by linarith
    have e : (2 * (H : ℝ) * N * lN) ^ 2 = (H : ℝ) ^ 2 * (4 * N * lN) * (N * lN) := by ring
    rw [e, show (H : ℝ) ^ 3 * (4 * N * lN) = (H : ℝ) ^ 2 * (4 * N * lN) * H by ring]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hs2 : Real.sqrt ((H : ℝ) ^ 3 * (1 + N / 2)) ≤ H * N := by
    rw [show (H : ℝ) * N = Real.sqrt ((H * N) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have h1 : (H : ℝ) * (1 + N / 2) ≤ (N : ℝ) ^ 2 := by nlinarith
    have e : ((H : ℝ) * N) ^ 2 = (H : ℝ) ^ 2 * (N : ℝ) ^ 2 := by ring
    rw [e, show (H : ℝ) ^ 3 * (1 + N / 2) = (H : ℝ) ^ 2 * (H * (1 + N / 2)) by ring]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hdiv : |wsum N H y| ≤ 3 * H + 32 * N * lN + 16 * N + 18 * K₁ * N * (1 + lN) ^ 2 * L := by
    have h : (H : ℝ) * |wsum N H y| ≤ H * (3 * H + 32 * N * lN + 16 * N + 18 * K₁ * N * (1 + lN) ^ 2 * L) := by
      refine htot.trans ?_
      nlinarith
    exact le_of_mul_le_mul_left h hH0
  have hL0 : (1 : ℝ) / 2 ≤ L := by linarith
  have hsqL : (1 + lN) ^ 2 ≤ 4 * lN ^ 2 := by nlinarith
  have hP : lN ≤ lN ^ 2 := by nlinarith
  have h3 : 18 * K₁ * N * (1 + lN) ^ 2 * L ≤ 72 * K₁ * N * lN ^ 2 * L := by
    have := mul_le_mul_of_nonneg_left hsqL (show (0 : ℝ) ≤ 18 * K₁ * N by positivity)
    have hL0' : 0 ≤ L := by linarith
    nlinarith
  have h4 : 3 * (H : ℝ) + 32 * N * lN + 16 * N ≤ 51 * N * lN := by nlinarith
  have h5 : 51 * (N : ℝ) * lN ≤ 110 * N * lN ^ 2 * L := by
    have : (1 : ℝ) / 2 * lN ≤ lN ^ 2 * L := by nlinarith
    nlinarith
  nlinarith

end LeanLab.LZCesaroShort
