import LeanLab.RieselVaughan1983.Lemma1BandsDeep

/-!
# P0032 Lemma 1 for `x ≥ 2`, and the full Lemma 1 under two labels

Session PC 20261021T0003Z-5661, unit U-1325, paper P0032 Riesel-Vaughan 1983, track T1.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here bears on it directly.

The Stieltjes constant `γ₁` stays the parameter `g1` of `lem1E`; here it is tied to its
definition by the hypothesis `hL : (∑_{m≤n} log m / m) − ½ log² n → g1`. For `g1 ≠ γ₁` the
Lemma 1 bound is false for large `x`, as `E(x) → 2(g1 − γ₁)`, so some such link is needed.

Route, a variant of p. 49. With `z = √x`, `N = ⌊z⌋`, `X = ⌊x⌋`, the hyperbola identity
`∑_{m≤X} d(m)/m = 2 ∑_{a≤N} H(X/a)/a − H(N)²` and the exact algebra
`E(x) = 2 log N·ρ + λ/N + 2λρ − λ² − 2σ − R² + 2 ∑_{a≤N} r_a/a`, where
`ρ = H_N − log N − 1/(2N) − γ₀ ∈ [−1/(8N²), 0]`, `λ = log(z/N) ∈ [0, 1/N]`,
`σ = c_N − γ₁` with `c_n = ∑_{m≤n} log m/m − ½log² n − log n/(2n)`, `|σ| ≤ 1/(10N)`,
`R = 1/(2N) + ρ − λ` and `r_a = H(⌊x/a⌋) − log(x/a) − γ₀`, `|r_a| ≤ a/(2x) + a²/x²`.
The cancellation of the `B₁` terms of p. 49 is the vanishing of the `log N · λ` terms.
Together `|E(x)| < 2/N ≤ 1.641 x^{-1/3}` for `N ≥ 4`, theorem `lemma1_ge16`.

`2 ≤ x < 16`: fourteen bands `n ≤ x < n+1`, the sum `∑_{m≤n} d(m)/m` by `decide +kernel` in `ℚ`,
`log n` by chaining `log(k+1) − log k ∈ [2/(2k+1), 2/(2k+1) + 1/(6(2k+1)k(k+1))]` from Mathlib's
`log 2`, and `|E| < 0.65 < 1.641·16^{-1/3}`, theorem `lemma1_2_16`, CONDITIONAL ON
`−0.08 < γ₁ < −0.07`. `lemma1_full` gives `Lemma1P g1` CONDITIONAL ON `hL` and the CITED range
`−0.0729 < γ₁ < −0.07`, using `lemma1_lt_two` of `Lemma1BandsDeep` below `x = 2`.
-/

namespace LeanLab.RieselVaughan1983

open Real Finset Filter Topology

/-! ## Two sided bounds for `H_m` -/

lemma log_one_add_inv_ge (n : ℕ) (hn : 0 < n) :
    2 / (2 * (n : ℝ) + 1) ≤ Real.log (1 + (n : ℝ)⁻¹) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.hasSum_log_one_add_inv (a := (n : ℝ)) (by linarith)
  have h := le_hasSum hs 0 (fun j _ => by positivity)
  simp only [Nat.cast_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at h
  have : 2 / (2 * (n : ℝ) + 1) = 2 * (1 / (2 * n + 1)) := by ring
  linarith

lemma emSeq_succ_le (k : ℕ) :
    emSeq (k + 1) + 1 / (8 * (((k + 1 : ℕ) : ℝ) + 1) ^ 2) ≤ emSeq k + 1 / (8 * ((k : ℝ) + 1) ^ 2) := by
  have hL := log_one_add_inv_ge (k + 1) (Nat.succ_pos k)
  set n : ℝ := ((k + 1 : ℕ) : ℝ) with hn
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast Nat.succ_pos k
  have hlog : Real.log (n + 1) = Real.log n + Real.log (1 + n⁻¹) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  have hH : (harmonic (k + 2) : ℝ) = harmonic (k + 1) + 1 / (n + 1) := by
    rw [harmonic_succ]; push_cast; rw [hn]; push_cast; ring
  unfold emSeq
  have e1 : ((k : ℝ) + 1) = n := by rw [hn]; push_cast; ring
  have e2 : (((k + 1 : ℕ) : ℝ) + 1) = n + 1 := by rw [hn]
  rw [e1, e2, hH, hlog]
  have key : 1 / (n + 1) - 1 / (2 * (n + 1)) + 1 / (2 * n) - 2 / (2 * n + 1)
      ≤ 1 / (8 * n ^ 2) - 1 / (8 * (n + 1) ^ 2) := by
    have h0 : 0 < n := by linarith
    rw [show 1 / (n + 1) - 1 / (2 * (n + 1)) + 1 / (2 * n) - 2 / (2 * n + 1)
        = 1 / (2 * n * (n + 1) * (2 * n + 1)) by field_simp; ring,
      show 1 / (8 * n ^ 2) - 1 / (8 * (n + 1) ^ 2) = (2 * n + 1) / (8 * n ^ 2 * (n + 1) ^ 2) by
        field_simp; ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos h0 (by positivity : (0:ℝ) < n + 1), pow_pos h0 3, pow_pos h0 4]
  linarith

lemma gamma_le_emSeq (k : ℕ) :
    eulerMascheroniConstant ≤ emSeq k + 1 / (8 * ((k : ℝ) + 1) ^ 2) := by
  have hanti : Antitone (fun k : ℕ => emSeq k + 1 / (8 * ((k : ℝ) + 1) ^ 2)) := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    have := emSeq_succ_le k
    simpa using this
  have hz : Tendsto (fun k : ℕ => 1 / (8 * ((k : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine squeeze_zero (fun k => by positivity) (fun k => ?_) h
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have ht := tendsto_emSeq.add hz
  rw [add_zero] at ht
  exact hanti.le_of_tendsto ht k

lemma harm_bounds (m : ℕ) (hm : 1 ≤ m) :
    Real.log m + 1 / (2 * m) - 1 / (8 * (m : ℝ) ^ 2) + eulerMascheroniConstant
        ≤ (harmonic m : ℝ) ∧
      (harmonic m : ℝ) ≤ Real.log m + 1 / (2 * m) + eulerMascheroniConstant := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 := emSeq_le_gamma k
  have h2 := gamma_le_emSeq k
  unfold emSeq at h1 h2
  push_cast
  constructor <;> linarith

/-- `|H(⌊y⌋) − log y − γ₀| ≤ 1/(2y) + 1/y²` for `y ≥ 4`. -/
lemma R_bound (y : ℝ) (hy : 4 ≤ y) :
    |(harmonic ⌊y⌋₊ : ℝ) - Real.log y - eulerMascheroniConstant| ≤ 1 / (2 * y) + 1 / y ^ 2 := by
  set m := ⌊y⌋₊ with hmdef
  have hm4 : 4 ≤ m := Nat.le_floor (by norm_num; linarith)
  have hmy : (m : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hym : y < m + 1 := Nat.lt_floor_add_one y
  have hm4' : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  obtain ⟨hl, hu⟩ := harm_bounds m (by omega)
  have hm0 : (0 : ℝ) < m := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hlu : Real.log y - Real.log m ≤ (y - m) / m := by
    rw [← Real.log_div hy0.ne' hm0.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < y / m by positivity)
    rw [show y / m - 1 = (y - m) / m by field_simp] at this; exact this
  have hll : (y - m) / y ≤ Real.log y - Real.log m := by
    rw [← Real.log_div hy0.ne' hm0.ne']
    have := Real.one_sub_inv_le_log_of_pos (show 0 < y / m by positivity)
    rw [show 1 - (y / m)⁻¹ = (y - m) / y by field_simp] at this; exact this
  have k1 : 1 / (2 * (m : ℝ)) - (y - m) / y ≤ 1 / (2 * y) := by
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [mul_pos hm0 hy0, mul_nonneg (mul_nonneg hm0.le hy0.le) (sub_nonneg.mpr hmy)]
  have k2 : -(1 / (2 * y)) - 1 / y ^ 2 ≤ 1 / (2 * (m : ℝ)) - 1 / (8 * (m : ℝ) ^ 2) - (y - m) / m := by
    have hθ0 : 0 ≤ y - m := by linarith
    have hθ1 : y - m < 1 := by linarith
    have e : 1 / (2 * (m : ℝ)) - 1 / (8 * (m : ℝ) ^ 2) - (y - m) / m - (-(1 / (2 * y)) - 1 / y ^ 2)
        = (4 * m * y ^ 2 - y ^ 2 - 8 * m * (y - m) * y ^ 2 + 4 * m ^ 2 * y + 8 * m ^ 2)
          / (8 * m ^ 2 * y ^ 2) := by
      field_simp; ring
    have hnum : 0 ≤ 4 * m * y ^ 2 - y ^ 2 - 8 * m * (y - m) * y ^ 2 + 4 * m ^ 2 * y
        + 8 * (m : ℝ) ^ 2 := by
      -- worst case `y → m + 1`; the numerator is decreasing in `y` on `[m, m+1]`
      have hd : 0 ≤ (m + 1 - y) := by linarith
      nlinarith [mul_nonneg hd hm0.le, mul_nonneg (mul_nonneg hd hm0.le) hm0.le,
        mul_nonneg (mul_nonneg hd hm0.le) hy0.le, mul_nonneg (mul_nonneg hd hy0.le) hy0.le,
        mul_nonneg (mul_nonneg (mul_nonneg hd hm0.le) hy0.le) hy0.le,
        mul_nonneg (mul_nonneg (mul_nonneg hd hm0.le) hm0.le) hy0.le,
        mul_nonneg (mul_nonneg hθ0 hm0.le) hy0.le, mul_nonneg hθ0 hm0.le,
        mul_nonneg (mul_nonneg (mul_nonneg hθ0 hm0.le) hy0.le) hy0.le]
    have : 0 ≤ 1 / (2 * (m : ℝ)) - 1 / (8 * (m : ℝ) ^ 2) - (y - m) / m - (-(1 / (2 * y)) - 1 / y ^ 2) := by
      rw [e]; positivity
    linarith
  have hy2 : 0 ≤ 1 / y ^ 2 := by positivity
  rw [abs_le]; constructor <;> nlinarith

/-! ## The `γ₁` sequence `c_n` -/

/-- `∑_{m≤n} log m / m`. -/
noncomputable def Lsum (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, Real.log m / m

/-- `c_n = ∑_{m≤n} log m / m − ½ log² n − log n / (2n)`. -/
noncomputable def cseq (n : ℕ) : ℝ := Lsum n - Real.log n ^ 2 / 2 - Real.log n / (2 * n)

lemma log_le_div_e (k : ℝ) (hk : 0 < k) : Real.log k ≤ k / (27 / 10) := by
  have he := Real.exp_one_gt_d9
  have h := Real.log_le_sub_one_of_pos (show 0 < k / Real.exp 1 by positivity)
  rw [Real.log_div hk.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  have : k / Real.exp 1 ≤ k / (27 / 10) :=
    div_le_div_of_nonneg_left hk.le (by norm_num) (by linarith)
  linarith

lemma poly_P0 (k : ℝ) (hk' : 2 ≤ k) :
    5 * (12 * k * (k + 1) + 1) * (6 * k + 1) ≤ 36 * (2 * k + 1) ^ 2 * k * (k + 1) := by
  have hk0 : 0 < k := by linarith
  nlinarith [mul_pos hk0 (by positivity : (0:ℝ) < k + 1), pow_pos hk0 3, pow_pos hk0 4,
    mul_nonneg (sub_nonneg.mpr hk') (pow_pos hk0 3).le,
    mul_nonneg (sub_nonneg.mpr hk') (pow_pos hk0 2).le,
    mul_nonneg (sub_nonneg.mpr hk') hk0.le]

set_option maxHeartbeats 1000000 in
lemma cseq_step (k : ℕ) (hk : 2 ≤ k) :
    |cseq (k + 1) - cseq k| ≤ 1 / (10 * (k : ℝ)) - 1 / (10 * ((k : ℝ) + 1)) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hLs : Lsum (k + 1) = Lsum k + Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) := by
    unfold Lsum; rw [Finset.sum_Icc_succ_top (by omega)]; push_cast; ring
  have hd1 := log_one_add_inv_ge k (by omega)
  have hd2 := log_one_add_inv_le k (by omega)
  have hlog : Real.log ((k : ℝ) + 1) = Real.log k + Real.log (1 + (k : ℝ)⁻¹) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  have hlk := log_le_div_e k hk0
  have hl0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  set l := Real.log (k : ℝ)
  set d := Real.log (1 + (k : ℝ)⁻¹)
  unfold cseq; rw [hLs]; push_cast; rw [hlog]
  have hΔ : Lsum k + (l + d) / (k + 1) - (l + d) ^ 2 / 2 - (l + d) / (2 * (k + 1))
      - (Lsum k - l ^ 2 / 2 - l / (2 * k))
      = l / 2 * (1 / (k + 1) + 1 / k - 2 * d) + (d / (k + 1) - d ^ 2) / 2 := by
    field_simp; ring
  rw [hΔ]
  -- the bracket `P = 1/(k+1) + 1/k − 2d` lies in `[0, 1/(k(k+1)(2k+1))]`
  have hd1' : 2 ≤ d * (2 * k + 1) := by
    rw [div_le_iff₀ (by positivity)] at hd1; linarith
  have hd2' : d * (6 * (2 * k + 1) * k * (k + 1)) ≤ 12 * k * (k + 1) + 1 := by
    have e : 2 / (2 * (k : ℝ) + 1) + 1 / (6 * (2 * k + 1) * k * (k + 1))
        = (12 * k * (k + 1) + 1) / (6 * (2 * k + 1) * k * (k + 1)) := by field_simp; ring
    rw [e, le_div_iff₀ (by positivity)] at hd2; linarith
  have hP : 1 / ((k : ℝ) + 1) + 1 / k - 2 * d
      = ((2 * k + 1) ^ 2 - 2 * d * k * (k + 1) * (2 * k + 1)) / (k * (k + 1) * (2 * k + 1)) := by
    field_simp; ring
  have hP0 : 0 ≤ (2 * (k : ℝ) + 1) ^ 2 - 2 * d * k * (k + 1) * (2 * k + 1) := by nlinarith
  have hP1 : (2 * (k : ℝ) + 1) ^ 2 - 2 * d * k * (k + 1) * (2 * k + 1) ≤ 1 := by
    nlinarith [mul_pos hk0 (by positivity : (0:ℝ) < k + 1)]
  have hT : 1 / (10 * (k : ℝ)) - 1 / (10 * ((k : ℝ) + 1)) = 1 / (10 * k * (k + 1)) := by
    field_simp; ring
  rw [hT, hP]
  set q := (2 * (k : ℝ) + 1) ^ 2 - 2 * d * k * (k + 1) * (2 * k + 1)
  have hden : (0 : ℝ) < k * (k + 1) * (2 * k + 1) := by positivity
  -- first term in `[0, 1/(20 k (k+1))]`
  have t1a : 0 ≤ l / 2 * (q / (k * (k + 1) * (2 * k + 1))) := by positivity
  have t1b : l / 2 * (q / (k * (k + 1) * (2 * k + 1))) ≤ 1 / (10 * k * (k + 1)) := by
    have : l / 2 * (q / (k * (k + 1) * (2 * k + 1))) ≤ l / 2 * (1 / (k * (k + 1) * (2 * k + 1))) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hP1 hden.le) (by positivity)
    refine this.trans ?_
    rw [show l / 2 * (1 / (k * (k + 1) * (2 * k + 1))) = l / (2 * (k * (k + 1) * (2 * k + 1))) by
      field_simp, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hk0 (by positivity : (0:ℝ) < k + 1)]
  -- second term in `[−1/(10 k (k+1)), 0]`
  have hdk : 1 / ((k : ℝ) + 1) ≤ d := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hd0 : 0 ≤ d := le_trans (by positivity) hdk
  have t2a : (d / (k + 1) - d ^ 2) / 2 ≤ 0 := by
    have : d / ((k : ℝ) + 1) = d * (1 / (k + 1)) := by ring
    rw [this]; nlinarith
  have t2b : -(1 / (10 * k * (k + 1))) ≤ (d / (k + 1) - d ^ 2) / 2 := by
    have e1 : (d / ((k : ℝ) + 1) - d ^ 2) / 2 = -(d * (d * (k + 1) - 1)) / (2 * (k + 1)) := by
      field_simp; ring
    rw [e1, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
    have hA : 0 ≤ d * (k + 1) - 1 := by
      rw [div_le_iff₀ (by positivity)] at hdk; linarith
    obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 6 * (2 * (k : ℝ) + 1) * k * (k + 1) := ⟨_, rfl⟩
    have hD : 0 < D := by rw [hDdef]; positivity
    have hdD : d * D ≤ 12 * k * (k + 1) + 1 := by rw [hDdef]; linarith
    have heD : (d * (k + 1) - 1) * D ≤ (k + 1) * (6 * k + 1) := by
      have : (d * (k + 1) - 1) * D = (d * D) * (k + 1) - D := by ring
      rw [this, hDdef]; rw [hDdef] at hdD; nlinarith
    have Q : (d * (d * (k + 1) - 1)) * D ^ 2 ≤ (12 * k * (k + 1) + 1) * ((k + 1) * (6 * k + 1)) := by
      have : (d * (d * (k + 1) - 1)) * D ^ 2 = (d * D) * ((d * (k + 1) - 1) * D) := by ring
      rw [this]
      exact mul_le_mul hdD heD (by positivity) (by positivity)
    have P0 := poly_P0 k hk'
    have P : 5 * k * ((12 * (k : ℝ) * (k + 1) + 1) * ((k + 1) * (6 * k + 1))) ≤ D ^ 2 := by
      have hkk : 0 < (k : ℝ) * (k + 1) := by positivity
      have : D ^ 2 = (36 * (2 * k + 1) ^ 2 * k * (k + 1)) * (k * (k + 1)) := by rw [hDdef]; ring
      rw [this]
      have e : 5 * k * ((12 * (k : ℝ) * (k + 1) + 1) * ((k + 1) * (6 * k + 1)))
          = (5 * (12 * (k : ℝ) * (k + 1) + 1) * (6 * k + 1)) * (k * (k + 1)) := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right P0 hkk.le
    have hde0 : 0 ≤ d * (d * (k + 1) - 1) := mul_nonneg hd0 hA
    have R5 : (5 * k * (d * (d * (k + 1) - 1))) * D ^ 2 ≤ 1 * D ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left Q (by positivity : (0:ℝ) ≤ 5 * k)
      calc (5 * (k : ℝ) * (d * (d * (k + 1) - 1))) * D ^ 2
          = 5 * (k : ℝ) * ((d * (d * (k + 1) - 1)) * D ^ 2) := by ring
        _ ≤ 5 * (k : ℝ) * ((12 * k * (k + 1) + 1) * ((k + 1) * (6 * k + 1))) := h1
        _ ≤ D ^ 2 := P
        _ = 1 * D ^ 2 := by ring
    have R6 : 5 * k * (d * (d * (k + 1) - 1)) ≤ 1 :=
      le_of_mul_le_mul_right R5 (by positivity)
    calc d * (d * ((k : ℝ) + 1) - 1) * (10 * k * (k + 1))
        = (5 * (k : ℝ) * (d * (d * (k + 1) - 1))) * (2 * (k + 1)) := by ring
      _ ≤ 1 * (2 * ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_right R6 (by positivity)
  rw [abs_le]; constructor <;> linarith

lemma cseq_tendsto (g1 : ℝ)
    (hL : Tendsto (fun n : ℕ => Lsum n - Real.log n ^ 2 / 2) atTop (𝓝 g1)) :
    Tendsto cseq atTop (𝓝 g1) := by
  have h0 : Tendsto (fun n : ℕ => Real.log n / (2 * n)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 2 0 1 (by norm_num)).comp
      tendsto_natCast_atTop_atTop
    refine h.congr (fun n => ?_)
    simp
  have := hL.sub h0
  rw [sub_zero] at this
  exact this.congr (fun n => by unfold cseq; ring)

lemma tendsto_inv_ten (c : ℝ) :
    Tendsto (fun j : ℕ => 1 / (10 * ((j : ℝ) + c))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun j : ℕ => 10 * ((j : ℝ) + c)) atTop atTop :=
    (tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num)
  have := h1.inv_tendsto_atTop
  exact this.congr (fun j => by simp [one_div])

/-- `|c_n − γ₁| ≤ 1/(10n)` for `n ≥ 2`, CONDITIONAL ON `hL`, the definition of `γ₁`. -/
lemma sigma_bound (g1 : ℝ)
    (hL : Tendsto (fun n : ℕ => Lsum n - Real.log n ^ 2 / 2) atTop (𝓝 g1))
    (n : ℕ) (hn : 2 ≤ n) : |cseq n - g1| ≤ 1 / (10 * (n : ℝ)) := by
  have ht := cseq_tendsto g1 hL
  have hc2 : Tendsto (fun j : ℕ => cseq (j + 2)) atTop (𝓝 g1) :=
    (tendsto_add_atTop_iff_nat 2).mpr ht
  have hz := tendsto_inv_ten 2
  have hu : Monotone (fun j : ℕ => cseq (j + 2) - 1 / (10 * ((j : ℝ) + 2))) := by
    refine monotone_nat_of_le_succ (fun j => ?_)
    have h := cseq_step (j + 2) (by omega)
    rw [abs_le] at h
    push_cast at h ⊢
    have e : ((j : ℝ) + 1 + 2) = (j + 2) + 1 := by ring
    rw [e]; linarith [h.1]
  have hv : Antitone (fun j : ℕ => cseq (j + 2) + 1 / (10 * ((j : ℝ) + 2))) := by
    refine antitone_nat_of_succ_le (fun j => ?_)
    have h := cseq_step (j + 2) (by omega)
    rw [abs_le] at h
    push_cast at h ⊢
    have e : ((j : ℝ) + 1 + 2) = (j + 2) + 1 := by ring
    rw [e]; linarith [h.2]
  have hut := hc2.sub hz
  have hvt := hc2.add hz
  rw [sub_zero] at hut; rw [add_zero] at hvt
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have a1 := hu.ge_of_tendsto hut j
  have a2 := hv.le_of_tendsto hvt j
  push_cast
  rw [abs_le]; constructor <;> linarith

/-! ## The divisor sum by the hyperbola method -/

lemma divisors_succ_eq (X : ℕ) :
    (X + 1).divisors = insert (X + 1) ((Icc 1 X).filter (· ∣ X + 1)) := by
  ext d
  simp only [Nat.mem_divisors, mem_insert, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hd, -⟩
    have h1 := Nat.pos_of_dvd_of_pos hd (Nat.succ_pos X)
    have h2 := Nat.le_of_dvd (Nat.succ_pos X) hd
    by_cases h : d = X + 1
    · left; exact h
    · right; exact ⟨⟨h1, by omega⟩, hd⟩
  · rintro (h | ⟨-, hd⟩)
    · exact ⟨h ▸ dvd_refl _, by omega⟩
    · exact ⟨hd, by omega⟩

/-- `∑_{m≤X} d(m)/m = ∑_{a≤X} H(⌊X/a⌋)/a`. -/
lemma divsum_eq (X : ℕ) : ∑ m ∈ Icc 1 X, ((m.divisors.card : ℝ) / m) =
    ∑ a ∈ Icc 1 X, (harmonic (X / a) : ℝ) / a := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega)]
    have hstep : ∀ a ∈ Icc 1 X, (harmonic ((X + 1) / a) : ℝ) / a
        = (harmonic (X / a) : ℝ) / a + (if a ∣ X + 1 then 1 / ((X : ℝ) + 1) else 0) := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.1
      rw [Nat.succ_div]
      split_ifs with h
      · rw [harmonic_succ]
        have hm : (X / a + 1) * a = X + 1 := by
          rw [← Nat.succ_div_of_dvd h]; exact Nat.div_mul_cancel h
        have hm' : ((X / a : ℕ) + 1 : ℝ) * a = (X : ℝ) + 1 := by exact_mod_cast hm
        push_cast
        rw [add_div]; congr 1
        rw [← hm']; field_simp
      · simp
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_ite, sum_const_zero,
      add_zero, sum_const, nsmul_eq_mul, Nat.div_self (Nat.succ_pos X), divisors_succ_eq,
      card_insert_of_notMem (by simp)]
    push_cast
    simp only [Nat.cast_add, Nat.cast_one, harmonic_succ, harmonic_zero]
    push_cast
    field_simp
    ring

lemma sum_Icc_inv (n : ℕ) : (harmonic n : ℝ) = ∑ b ∈ Icc 1 n, (1 : ℝ) / b := by
  rw [harmonic_eq_sum_Icc]; push_cast; simp

/-- Dirichlet's hyperbola identity in the form used for Lemma 1. -/
lemma hyperbola (X N : ℕ) (h1 : N * N ≤ X) (h2 : X < (N + 1) * (N + 1)) :
    ∑ a ∈ Icc 1 X, (harmonic (X / a) : ℝ) / a =
      2 * ∑ a ∈ Icc 1 N, (harmonic (X / a) : ℝ) / a - (harmonic N : ℝ) ^ 2 := by
  have hNX : N ≤ X := le_trans (Nat.le_mul_self N) h1
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 X) (fun a => a ≤ N)]
  have hf1 : (Icc 1 X).filter (fun a => a ≤ N) = Icc 1 N := by
    ext a; simp only [mem_filter, mem_Icc]; omega
  rw [hf1]
  have hexp : ∀ a : ℕ, (harmonic (X / a) : ℝ) / a = ∑ b ∈ Icc 1 (X / a), (1 : ℝ) / a * (1 / b) := by
    intro a; rw [sum_Icc_inv, Finset.sum_div]
    refine sum_congr rfl (fun b _ => by ring)
  have h2nd : ∑ a ∈ (Icc 1 X).filter (fun a => ¬ a ≤ N), (harmonic (X / a) : ℝ) / a
      = ∑ b ∈ Icc 1 N, ((harmonic (X / b) : ℝ) - harmonic N) / b := by
    calc _ = ∑ a ∈ (Icc 1 X).filter (fun a => ¬ a ≤ N), ∑ b ∈ Icc 1 (X / a),
            (1 : ℝ) / a * (1 / b) := sum_congr rfl (fun a _ => hexp a)
      _ = ∑ b ∈ Icc 1 N, ∑ a ∈ (Icc 1 (X / b)).filter (fun a => ¬ a ≤ N),
            (1 : ℝ) / a * (1 / b) := by
          apply Finset.sum_comm'
          intro a b
          simp only [mem_filter, mem_Icc]
          constructor
          · rintro ⟨⟨⟨ha1, haX⟩, haN⟩, hb1, hbX⟩
            rw [Nat.le_div_iff_mul_le (by omega)] at hbX
            refine ⟨⟨⟨ha1, ?_⟩, haN⟩, hb1, ?_⟩
            · rw [Nat.le_div_iff_mul_le (by omega)]; rw [mul_comm]; exact hbX
            · by_contra hc; push Not at hc
              have : (N + 1) * (N + 1) ≤ b * a := Nat.mul_le_mul hc (by omega)
              omega
          · rintro ⟨⟨⟨ha1, haX⟩, haN⟩, hb1, hbN⟩
            rw [Nat.le_div_iff_mul_le (by omega)] at haX
            refine ⟨⟨⟨ha1, ?_⟩, haN⟩, hb1, ?_⟩
            · nlinarith
            · rw [Nat.le_div_iff_mul_le (by omega)]; rw [mul_comm]; exact haX
      _ = _ := by
          refine sum_congr rfl (fun b hb => ?_)
          rw [Finset.mem_Icc] at hb
          have hbN : N ≤ X / b := by
            rw [Nat.le_div_iff_mul_le (by omega)]
            exact le_trans (Nat.mul_le_mul_left N hb.2) h1
          have hsub := Finset.sum_filter_add_sum_filter_not (Icc 1 (X / b)) (fun a => a ≤ N)
            (fun a => (1 : ℝ) / a * (1 / b))
          have hf2 : (Icc 1 (X / b)).filter (fun a => a ≤ N) = Icc 1 N := by
            ext a; simp only [mem_filter, mem_Icc]; omega
          rw [hf2] at hsub
          have e1 : ∑ a ∈ Icc 1 (X / b), (1 : ℝ) / a * (1 / b) = (harmonic (X / b) : ℝ) / b := by
            rw [← Finset.sum_mul, ← sum_Icc_inv]; ring
          have e2 : ∑ a ∈ Icc 1 N, (1 : ℝ) / a * (1 / b) = (harmonic N : ℝ) / b := by
            rw [← Finset.sum_mul, ← sum_Icc_inv]; ring
          rw [sub_div]; linarith
  have h3 : ∑ b ∈ Icc 1 N, ((harmonic (X / b) : ℝ) - harmonic N) / b
      = ∑ b ∈ Icc 1 N, (harmonic (X / b) : ℝ) / b - (harmonic N : ℝ) ^ 2 := by
    calc _ = ∑ b ∈ Icc 1 N, ((harmonic (X / b) : ℝ) / b - (harmonic N : ℝ) * (1 / b)) :=
          sum_congr rfl (fun b _ => by ring)
      _ = ∑ b ∈ Icc 1 N, (harmonic (X / b) : ℝ) / b - (harmonic N : ℝ) * ∑ b ∈ Icc 1 N, (1 : ℝ) / b := by
          rw [sum_sub_distrib, ← mul_sum]
      _ = _ := by rw [← sum_Icc_inv, sq]
  rw [h2nd, h3]; ring

/-! ## Assembly -/

set_option maxHeartbeats 1000000 in
/-- The algebra of p. 49: `E = 2 log N·ρ + λ/N + 2λρ − λ² − 2σ − R² + 2 Sr`, and its size. -/
lemma final_alg (lN lam ρ σ Sr u γ g1 H L t : ℝ)
    (hH : H = lN + u / 2 + γ + ρ) (ht : t = 2 * (lN + lam))
    (hL : L = g1 + σ + lN ^ 2 / 2 + lN * u / 2)
    (hu0 : 0 < u) (hu1 : u ≤ 1 / 4) (hρl : -(u ^ 2 / 8) ≤ ρ) (hρu : ρ ≤ 0)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ u) (hσ : |σ| ≤ u / 10) (hS : |Sr| ≤ u / 2 + u ^ 2)
    (hlN0 : 0 ≤ lN) (hlNu : lN * u ≤ 10 / 27) :
    |2 * ((t + γ) * H - L + Sr) - H ^ 2 - 1 / 2 * t ^ 2 - 2 * γ * t - γ ^ 2 + 2 * g1| < 2 * u := by
  obtain ⟨R, hR⟩ : ∃ R, R = u / 2 + ρ - lam := ⟨_, rfl⟩
  have hE : 2 * ((t + γ) * H - L + Sr) - H ^ 2 - 1 / 2 * t ^ 2 - 2 * γ * t - γ ^ 2 + 2 * g1
      = 2 * (lN * ρ) + lam * (u - lam) + 2 * (lam * ρ) - 2 * σ - R ^ 2 + 2 * Sr := by
    subst hH ht hL hR; ring
  rw [hE]
  have hu2 : u ^ 2 ≤ u / 4 := by nlinarith
  have hu3 : u ^ 3 ≤ u / 16 := by nlinarith
  have hA : -(u / 21) ≤ lN * ρ := by
    have h1 := mul_le_mul_of_nonneg_left hρl hlN0
    have h2 : lN * u * u ≤ 10 / 27 * u := mul_le_mul_of_nonneg_right hlNu hu0.le
    nlinarith
  have hA' : lN * ρ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlN0 hρu
  have hB : 0 ≤ lam * (u - lam) := mul_nonneg hl0 (by linarith)
  have hB' : lam * (u - lam) ≤ u ^ 2 / 4 := by nlinarith [sq_nonneg (lam - u / 2)]
  have hC : -(u ^ 3 / 8) ≤ lam * ρ := by
    have h1 := mul_le_mul_of_nonneg_left hρl hl0
    have h2 : lam * u ^ 2 ≤ u * u ^ 2 := mul_le_mul_of_nonneg_right hl1 (by positivity)
    nlinarith
  have hC' : lam * ρ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl0 hρu
  have hRl : -(u / 2 + u ^ 2 / 8) ≤ R := by rw [hR]; linarith
  have hRu : R ≤ u / 2 + u ^ 2 / 8 := by rw [hR]; nlinarith
  have hR2 : R ^ 2 ≤ 289 / 4096 * u := by
    have h1 : R ^ 2 ≤ (u / 2 + u ^ 2 / 8) ^ 2 := by
      exact sq_le_sq' (by linarith) hRu
    have h2 : u / 2 + u ^ 2 / 8 ≤ 17 / 32 * u := by nlinarith
    have h3 : (u / 2 + u ^ 2 / 8) ^ 2 ≤ (17 / 32 * u) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    nlinarith
  have hR20 : 0 ≤ R ^ 2 := sq_nonneg R
  rw [abs_le] at hσ hS
  rw [abs_lt]; constructor <;> linarith

lemma two_div_lt (x : ℝ) (N : ℕ) (hx0 : 0 < x) (hN4 : (4 : ℝ) ≤ N)
    (hxN : x < ((N : ℝ) + 1) * (N + 1)) : 2 * (1 / (N : ℝ)) < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hcube : x < (1641 * (N : ℝ) / 2000) ^ 3 := by
    have : ((N : ℝ) + 1) * (N + 1) ≤ (1641 * (N : ℝ) / 2000) ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hN4) (sq_nonneg (N : ℝ)),
        mul_nonneg (sub_nonneg.mpr hN4) hN0.le]
    linarith
  have hr : x ^ (1 / 3 : ℝ) < 1641 * (N : ℝ) / 2000 := by
    have h := Real.rpow_lt_rpow hx0.le hcube (by norm_num : (0 : ℝ) < 1 / 3)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at h
  have hp : 0 < x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hx0 _
  rw [Real.rpow_neg hx0.le, show 1641 / 1000 * (x ^ (1 / 3 : ℝ))⁻¹ = 1641 / (1000 * x ^ (1 / 3 : ℝ)) by
    field_simp, show 2 * (1 / (N : ℝ)) = 2 / N by ring, div_lt_div_iff₀ hN0 (by positivity)]
  nlinarith

/-- P0032 Lemma 1 for `x ≥ 16`: `|E(x)| < 1.641 x^{-1/3}`, in fact `|E(x)| < 2/⌊√x⌋`.
CONDITIONAL ON `hL`, which says that `g1` is the Stieltjes constant `γ₁`, defined as the limit
of `∑_{m≤n} log m / m − ½ log² n`. No numerical range of `γ₁` is used. -/
theorem lemma1_ge16 (g1 : ℝ)
    (hL : Tendsto (fun n : ℕ => Lsum n - Real.log n ^ 2 / 2) atTop (𝓝 g1))
    (x : ℝ) (hx : 16 ≤ x) : |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨z, hzdef⟩ : ∃ z, z = Real.sqrt x := ⟨_, rfl⟩
  have hzz : z * z = x := by rw [hzdef]; exact Real.mul_self_sqrt hx0.le
  have hz4 : 4 ≤ z := by
    rw [hzdef, show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  obtain ⟨N, hNdef⟩ : ∃ N, N = ⌊z⌋₊ := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X, X = ⌊x⌋₊ := ⟨_, rfl⟩
  have hN4 : 4 ≤ N := by rw [hNdef]; exact Nat.le_floor (by exact_mod_cast hz4)
  have hNz : (N : ℝ) ≤ z := by rw [hNdef]; exact Nat.floor_le (by linarith)
  have hzN : z < N + 1 := by rw [hNdef]; exact Nat.lt_floor_add_one z
  have hN4' : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < N := by linarith
  have hXx : (X : ℝ) ≤ x := by rw [hXdef]; exact Nat.floor_le hx0.le
  have hNNx : (N : ℝ) * N ≤ x := by nlinarith
  have hxNN : x < ((N : ℝ) + 1) * (N + 1) := by nlinarith
  have hN1 : N * N ≤ X := by
    rw [hXdef]; apply Nat.le_floor; push_cast; exact hNNx
  have hN2 : X < (N + 1) * (N + 1) := by
    have : (X : ℝ) < ((N + 1) * (N + 1) : ℕ) := by push_cast; linarith
    exact_mod_cast this
  unfold lem1E
  rw [← hXdef, divsum_eq, hyperbola X N hN1 hN2]
  have hsplit : ∑ a ∈ Icc 1 N, (harmonic (X / a) : ℝ) / a
      = (Real.log x + eulerMascheroniConstant) * (harmonic N : ℝ) - Lsum N
        + ∑ a ∈ Icc 1 N,
          ((harmonic ⌊x / a⌋₊ : ℝ) - Real.log (x / a) - eulerMascheroniConstant) / a := by
    rw [sum_Icc_inv N, Finset.mul_sum, Lsum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_Icc] at ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.1
    rw [Nat.floor_div_natCast, ← hXdef, Real.log_div hx0.ne' ha0.ne']
    field_simp; ring
  have hSr : |∑ a ∈ Icc 1 N,
      ((harmonic ⌊x / a⌋₊ : ℝ) - Real.log (x / a) - eulerMascheroniConstant) / a|
        ≤ 1 / (N : ℝ) / 2 + (1 / (N : ℝ)) ^ 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ a ∈ Icc 1 N,
        |((harmonic ⌊x / a⌋₊ : ℝ) - Real.log (x / a) - eulerMascheroniConstant) / a|
          ≤ 1 / (2 * x) + N / x ^ 2 := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.1
      have haN : (a : ℝ) ≤ N := by exact_mod_cast ha.2
      have hy4 : 4 ≤ x / a := by
        rw [le_div_iff₀ ha0]; nlinarith
      have hR := R_bound (x / a) hy4
      rw [abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
      have e : (1 / (2 * (x / a)) + 1 / (x / a) ^ 2) = (1 / (2 * x) + a / x ^ 2) * a := by
        field_simp
      rw [e] at hR
      have : (1 / (2 * x) + a / x ^ 2) * a ≤ (1 / (2 * x) + N / x ^ 2) * a := by
        apply mul_le_mul_of_nonneg_right _ ha0.le
        have : (a : ℝ) / x ^ 2 ≤ N / x ^ 2 := div_le_div_of_nonneg_right haN (by positivity)
        linarith
      linarith
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    have h1 : (N : ℝ) * (1 / (2 * x)) ≤ 1 / (N : ℝ) / 2 := by
      rw [show (N : ℝ) * (1 / (2 * x)) = N / (2 * x) by ring,
        show 1 / (N : ℝ) / 2 = 1 / (2 * N) by ring, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : (N : ℝ) * (N / x ^ 2) ≤ (1 / (N : ℝ)) ^ 2 := by
      rw [show (N : ℝ) * (N / x ^ 2) = (N * N) / x ^ 2 by ring, div_pow, one_pow,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : ((N : ℝ) * N) * ((N : ℝ) * N) ≤ x * x := mul_le_mul hNNx hNNx (by positivity) hx0.le
      nlinarith
    nlinarith
  rw [hsplit]
  obtain ⟨hHl, hHu⟩ := harm_bounds N (by omega)
  have hσ := sigma_bound g1 hL N (by omega)
  have hlam0 : 0 ≤ Real.log z - Real.log N := by
    have := Real.log_le_log hN0 hNz; linarith
  have hlam1 : Real.log z - Real.log N ≤ 1 / N := by
    rw [← Real.log_div (by linarith) hN0.ne']
    have h1 := Real.log_le_sub_one_of_pos (show 0 < z / N by positivity)
    have h2 : z / N - 1 ≤ 1 / N := by
      rw [div_sub_one hN0.ne', div_le_div_iff_of_pos_right hN0]; linarith
    linarith
  have hlogx : Real.log x = 2 * (Real.log N + (Real.log z - Real.log N)) := by
    rw [← hzz, Real.log_mul (by linarith) (by linarith)]; ring
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlN := log_le_div_e N hN0
  have hlNu : Real.log N * (1 / N) ≤ 10 / 27 := by
    rw [mul_one_div, div_le_iff₀ hN0]; linarith
  refine lt_of_lt_of_le (final_alg (Real.log N) (Real.log z - Real.log N)
    ((harmonic N : ℝ) - Real.log N - 1 / N / 2 - eulerMascheroniConstant) (cseq N - g1) _ (1 / N)
    eulerMascheroniConstant g1 _ _ _ (by ring) hlogx (by unfold cseq; ring) (by positivity)
    (by rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith) ?_ ?_ hlam0 hlam1
    (by rw [show (1 : ℝ) / N / 10 = 1 / (10 * N) by ring]; exact hσ) hSr hlN0 hlNu) ?_
  · rw [div_pow, one_pow]
    have : 1 / (8 * (N : ℝ) ^ 2) = 1 / N ^ 2 / 8 := by ring
    have h1 : 1 / (2 * (N : ℝ)) = 1 / N / 2 := by ring
    rw [this, h1] at hHl; linarith
  · have h1 : 1 / (2 * (N : ℝ)) = 1 / N / 2 := by ring
    rw [h1] at hHu; linarith
  · exact (two_div_lt x N hx0 hN4' hxNN).le

/-! ## The range `2 ≤ x < 16`, band by band -/

lemma log_step (k : ℕ) (hk : 1 ≤ k) :
    Real.log k + 2 / (2 * (k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) ∧
      Real.log ((k : ℝ) + 1) ≤ Real.log k + 2 / (2 * (k : ℝ) + 1)
        + 1 / (6 * (2 * (k : ℝ) + 1) * k * (k + 1)) := by
  have h1 := log_one_add_inv_ge k (by omega)
  have h2 := log_one_add_inv_le k (by omega)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : Real.log ((k : ℝ) + 1) = Real.log k + Real.log (1 + (k : ℝ)⁻¹) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  rw [hlog]; constructor <;> linarith

/-- Lemma 1 on one band `n ≤ x < n + 1 ≤ 16`, CONDITIONAL ON `−0.08 < γ₁ < −0.07`. -/
lemma small_band (g1 : ℝ) (hg1 : -8 / 100 < g1) (hg1' : g1 < -7 / 100) (n : ℕ) (D : ℚ) (a b : ℝ)
    (hn : 2 ≤ n) (hn16 : n + 1 ≤ 16)
    (hD : ∑ m ∈ Icc 1 n, ((m.divisors.card : ℚ) / m) = D)
    (ha0 : 0 ≤ a) (ha : a ≤ Real.log n) (hb : Real.log ((n : ℝ) + 1) ≤ b)
    (hup : (D : ℝ) - a ^ 2 / 2 - 2 * (57721 / 100000) * a - (57721 / 100000) ^ 2
      + 2 * (-7 / 100) < 65 / 100)
    (hlo : -(65 / 100) < (D : ℝ) - b ^ 2 / 2 - 2 * (5851 / 10000) * b - (5851 / 10000) ^ 2
      + 2 * (-8 / 100))
    (x : ℝ) (hx1 : (n : ℝ) ≤ x) (hx2 : x < n + 1) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn16' : (n : ℝ) + 1 ≤ 16 := by exact_mod_cast hn16
  have hx0 : 0 < x := by linarith
  have hfl : ⌊x⌋₊ = n := by
    rw [Nat.floor_eq_iff hx0.le]; exact ⟨hx1, hx2⟩
  have hDr : ∑ m ∈ Icc 1 n, ((m.divisors.card : ℝ) / m) = (D : ℝ) := by
    rw [← hD]; push_cast; rfl
  have hγ1 := gamma_gt_sharp
  have hγ2 := gamma_lt
  have hta : a ≤ Real.log x := ha.trans (Real.log_le_log (by linarith) hx1)
  have htb : Real.log x ≤ b := (Real.log_le_log hx0 hx2.le).trans hb
  -- the right side exceeds `0.65`
  have hcube : x < (63 / 25 : ℝ) ^ 3 := by norm_num; linarith
  have hr : x ^ (1 / 3 : ℝ) < 63 / 25 := by
    have h := Real.rpow_lt_rpow hx0.le hcube (by norm_num : (0 : ℝ) < 1 / 3)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at h
  have hp : 0 < x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hR : (65 / 100 : ℝ) < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
    rw [Real.rpow_neg hx0.le, show 1641 / 1000 * (x ^ (1 / 3 : ℝ))⁻¹
      = 1641 / (1000 * x ^ (1 / 3 : ℝ)) by field_simp, lt_div_iff₀ (by positivity)]
    nlinarith
  unfold lem1E
  rw [hfl, hDr]
  set t := Real.log x
  set γ := eulerMascheroniConstant
  have ht0 : 0 ≤ t := ha0.trans hta
  have e1 : a ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ha0 hta 2
  have e2 : 57721 / 100000 * a ≤ γ * t := mul_le_mul hγ1.le hta ha0 (by linarith)
  have e3 : (57721 / 100000 : ℝ) ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ (by norm_num) hγ1.le 2
  have f1 : t ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ht0 htb 2
  have f2 : γ * t ≤ 5851 / 10000 * b := mul_le_mul hγ2.le htb ht0 (by norm_num)
  have f3 : γ ^ 2 ≤ (5851 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hγ2.le 2
  rw [abs_lt]; constructor <;> nlinarith

/-- Lemma 1 on `2 ≤ x < 16`, CONDITIONAL ON `−0.08 < γ₁ < −0.07`. -/
theorem lemma1_2_16 (g1 : ℝ) (hg1 : -8 / 100 < g1) (hg1' : g1 < -7 / 100) (x : ℝ)
    (hx : 2 ≤ x) (hx' : x < 16) : |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have c2 := log_step 2 (by norm_num)
  norm_num at c2
  have c3 := log_step 3 (by norm_num)
  norm_num at c3
  have c4 := log_step 4 (by norm_num)
  norm_num at c4
  have c5 := log_step 5 (by norm_num)
  norm_num at c5
  have c6 := log_step 6 (by norm_num)
  norm_num at c6
  have c7 := log_step 7 (by norm_num)
  norm_num at c7
  have c8 := log_step 8 (by norm_num)
  norm_num at c8
  have c9 := log_step 9 (by norm_num)
  norm_num at c9
  have c10 := log_step 10 (by norm_num)
  norm_num at c10
  have c11 := log_step 11 (by norm_num)
  norm_num at c11
  have c12 := log_step 12 (by norm_num)
  norm_num at c12
  have c13 := log_step 13 (by norm_num)
  norm_num at c13
  have c14 := log_step 14 (by norm_num)
  norm_num at c14
  have c15 := log_step 15 (by norm_num)
  norm_num at c15
  obtain ⟨n, hn⟩ : ∃ n, n = ⌊x⌋₊ := ⟨_, rfl⟩
  have h1 : (n : ℝ) ≤ x := by rw [hn]; exact Nat.floor_le (by linarith)
  have h2 : x < n + 1 := by rw [hn]; exact Nat.lt_floor_add_one x
  have hn2 : 2 ≤ n := by rw [hn]; exact Nat.le_floor (by norm_num; linarith)
  have hn15 : n ≤ 15 := by
    have : (n : ℝ) < 16 := by linarith
    exact_mod_cast (show n < 16 by exact_mod_cast this) |> Nat.lt_succ_iff.mp
  clear hn
  interval_cases n
  · exact small_band g1 hg1 hg1' 2 (2 : ℚ) (6931 / 10000 : ℝ) (2747 / 2500 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 3 (8 / 3 : ℚ) (10931 / 10000 : ℝ) (2773 / 2000 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 4 (41 / 12 : ℚ) (3447 / 2500 : ℝ) (1006 / 625 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 5 (229 / 60 : ℚ) (1601 / 1000 : ℝ) (17919 / 10000 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 6 (269 / 60 : ℚ) (17829 / 10000 : ℝ) (19461 / 10000 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 7 (2003 / 420 : ℚ) (19367 / 10000 : ℝ) (5199 / 2500 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 8 (2213 / 420 : ℚ) (207 / 100 : ℝ) (10987 / 5000 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 9 (2353 / 420 : ℚ) (21877 / 10000 : ℝ) (23027 / 10000 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 10 (2521 / 420 : ℚ) (22929 / 10000 : ℝ) (23981 / 10000 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 11 (28571 / 4620 : ℚ) (11941 / 5000 : ℝ) (24851 / 10000 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 12 (30881 / 4620 : ℚ) (24751 / 10000 : ℝ) (25651 / 10000 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 13 (410693 / 60060 : ℚ) (25551 / 10000 : ℝ) (3299 / 1250 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 14 (427853 / 60060 : ℚ) (6573 / 2500 : ℝ) (13541 / 5000 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2
  · exact small_band g1 hg1 hg1' 15 (443869 / 60060 : ℚ) (13491 / 5000 : ℝ) (1733 / 625 : ℝ) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; linarith) (by push_cast; norm_num; linarith)
      (by push_cast; norm_num) (by push_cast; norm_num) x h1 h2

/-- P0032 Lemma 1, the full statement `Lemma1P`, CONDITIONAL ON `hL`, which identifies `g1` as
the Stieltjes constant `γ₁`, and on the CITED range `−0.0729 < γ₁ < −0.07`. -/
theorem lemma1_full (g1 : ℝ) (hg1 : -729 / 10000 < g1) (hg1' : g1 < -7 / 100)
    (hL : Tendsto (fun n : ℕ => Lsum n - Real.log n ^ 2 / 2) atTop (𝓝 g1)) : Lemma1P g1 := by
  intro x hx
  rcases lt_or_ge x 2 with h | h
  · exact lemma1_lt_two g1 hg1 hg1' x hx h
  rcases lt_or_ge x 16 with h' | h'
  · exact lemma1_2_16 g1 (by linarith) hg1' x h h'
  · exact lemma1_ge16 g1 hL x h'

end LeanLab.RieselVaughan1983
