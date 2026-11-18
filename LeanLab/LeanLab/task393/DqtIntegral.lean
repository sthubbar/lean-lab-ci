/-
Unit task393, helper file for the open leaf `leaf_dpt_W_le` of `DqtWeight.lean`.

Integral inputs for the weighted mean square of `Dpt δ y = fpt ((1+δ) y) - fpt y`, where
`fpt = ψ - θ` counts the prime powers `p^k`, `k ≥ 2`:
* `fpt_le_two_sqrt`: `fpt u ≤ 2 √u` for `u ≥ 10^13`, from Chebyshev's `θ x ≤ log 4 · x`.
* `int_Dpt_g_le`: the first moment of `Dpt` against the weight `min(1, (X/y)^3)` on `(2, B]`
  is at most `8.01 δ X √X`.
* `integrableOn_y_W`, `integral_y_W_le`: `∫_0^∞ y W(y/X) dy ≤ X²`.

Binary Goldbach is OPEN; nothing here is progress on it. These are standard estimates.
AI wrote the Lean code, Claude. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ChirreHagen2025.ThetaPsi
import LeanLab.ChirreHagen2025.SmoothY

namespace LeanLab.Task393
open Real MeasureTheory Set Chebyshev
open LeanLab.ChirreHagen2025 LeanLab.ChirreHagen2025.SmoothKernel

/-! ### `fpt u ≤ 2 √u` -/

/-- `log 40 ≤ 4`. Unit task393. -/
theorem log_forty_le : Real.log 40 ≤ 4 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
    pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) Real.exp_one_gt_d9.le) 4
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

/-- `log v ≤ v / 20` for `v ≥ 120`. Unit task393. -/
theorem log_le_div_twenty {v : ℝ} (hv : 120 ≤ v) : Real.log v ≤ v / 20 := by
  have hv0 : 0 < v := by linarith
  have h1 : Real.log (v / 40) ≤ v / 40 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hv0.ne' (by norm_num)] at h1
  linarith [log_forty_le]

/-- `ψ - θ ≤ 2 √u` for `u ≥ 10^13`. Unit task393. -/
theorem fpt_le_two_sqrt {u : ℝ} (hu : 10 ^ 13 ≤ u) : fpt u ≤ 2 * √u := by
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  set N := ⌊Real.log u / Real.log 2⌋₊ with hN
  rw [fpt_eq_sum hu1 (le_refl N)]
  set v := u ^ ((1 : ℝ) / 6) with hv
  have hv0 : 0 < v := Real.rpow_pos_of_pos hu0 _
  have hv6 : v ^ 6 = u := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have hv3 : v ^ 3 = √u := by
    rw [hv, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have hv2 : v ^ 2 = u ^ ((1 : ℝ) / 3) := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have hlog : Real.log u = 6 * Real.log v := by
    rw [hv, Real.log_rpow hu0]; ring
  have hv120 : 120 ≤ v := by
    by_contra h
    have h := not_le.mp h
    have h6 : v ^ 6 < 120 ^ 6 := pow_lt_pow_left₀ h hv0.le (by norm_num)
    rw [hv6] at h6
    norm_num at h6
    linarith
  have hlogv : Real.log v ≤ v / 20 := log_le_div_twenty hv120
  have hlogv0 : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
  have hterm : ∀ k ∈ Finset.Icc 2 N, θ (u ^ ((1 : ℝ) / k))
      ≤ Real.log 4 * v ^ 2 + (if k = 2 then Real.log 4 * v ^ 3 else 0) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hle := theta_le_log4_mul_x (x := u ^ ((1 : ℝ) / k)) (by positivity)
    split_ifs with h2
    · have e : u ^ ((1 : ℝ) / k) = v ^ 3 := by
        rw [hv3, Real.sqrt_eq_rpow, h2]; norm_num
      rw [e] at hle ⊢
      have : 0 ≤ Real.log 4 * v ^ 2 := mul_nonneg hl4 (by positivity)
      linarith
    · have hk3 : 3 ≤ k := by omega
      have e : u ^ ((1 : ℝ) / k) ≤ v ^ 2 := by
        rw [hv2]
        apply Real.rpow_le_rpow_of_exponent_le hu1
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast hk3
      have := mul_le_mul_of_nonneg_left e hl4
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hite : (∑ k ∈ Finset.Icc 2 N, (if k = 2 then Real.log 4 * v ^ 3 else 0))
      ≤ Real.log 4 * v ^ 3 := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact mul_nonneg hl4 (by positivity)
  have hNle : ((N + 1 - 2 : ℕ) : ℝ) ≤ 6 * Real.log v / Real.log 2 := by
    have h1 : ((N + 1 - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N + 1 - 2 ≤ N)
    have h2 : (N : ℝ) ≤ Real.log u / Real.log 2 :=
      Nat.floor_le (div_nonneg (Real.log_nonneg hu1) hl2.le)
    rw [hlog] at h2
    exact h1.trans h2
  have hc : ((N + 1 - 2 : ℕ) : ℝ) * (Real.log 4 * v ^ 2)
      ≤ 6 * Real.log v / Real.log 2 * (Real.log 4 * v ^ 2) :=
    mul_le_mul_of_nonneg_right hNle (mul_nonneg hl4 (by positivity))
  have hc2 : 6 * Real.log v / Real.log 2 * (Real.log 4 * v ^ 2) = 12 * Real.log v * v ^ 2 := by
    rw [h4]; field_simp; ring
  have hc3 : 12 * Real.log v * v ^ 2 ≤ 12 * (v / 20) * v ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hc4 : 12 * (v / 20) * v ^ 2 = 0.6 * v ^ 3 := by ring
  have hd : Real.log 4 * v ^ 3 ≤ 1.3863 * v ^ 3 :=
    mul_le_mul_of_nonneg_right (by rw [h4]; linarith [Real.log_two_lt_d9]) (by positivity)
  have hv3pos : 0 ≤ v ^ 3 := by positivity
  rw [← hv3]
  linarith

/-! ### The first moment of `Dpt` against `min(1, (X/y)^3)` -/

/-- Algebra for the tail: with `s = √X`. Unit task393. -/
theorem tail_alg {s u f : ℝ} (hs : 0 < s) (hu : 0 < u) (hf : f ≤ 2 * (u / s)) :
    f * (s * s / u) ^ 3 ≤ 2 * (s * s) ^ 2 * s * (u ^ 2)⁻¹ := by
  have h0 : 0 ≤ (s * s / u) ^ 3 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hf h0
  have h2 : 2 * (u / s) * (s * s / u) ^ 3 = 2 * (s * s) ^ 2 * s * (u ^ 2)⁻¹ := by
    field_simp
  linarith

/-- `fpt u (X/u)^3 ≤ 2 X² √X / u²` for `u ≥ X ≥ 10^13`. Unit task393. -/
theorem F_le {X u : ℝ} (hX : 10 ^ 13 ≤ X) (hu : X ≤ u) :
    fpt u * (X / u) ^ 3 ≤ 2 * X ^ 2 * √X * (u ^ 2)⁻¹ := by
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hu0 : 0 < u := lt_of_lt_of_le hX0 hu
  have hs : 0 < √X := Real.sqrt_pos.mpr hX0
  have hXs : X = √X * √X := (Real.mul_self_sqrt hX0.le).symm
  have h1 : fpt u ≤ 2 * √u := fpt_le_two_sqrt (hX.trans hu)
  have h2 : √X ≤ √u := Real.sqrt_le_sqrt hu
  have h3 : √u ≤ u / √X := by
    rw [le_div_iff₀ hs]
    calc √u * √X ≤ √u * √u := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg u)
      _ = u := Real.mul_self_sqrt hu0.le
  have h := tail_alg (s := √X) (u := u) (f := fpt u) hs hu0 (by linarith)
  rw [← hXs] at h
  exact h

/-- The weighted `fpt` is interval integrable away from 0. Unit task393. -/
theorem F_ii (X : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u => fpt u * (X / u) ^ 3) volume a b := by
  refine (fpt_mono.intervalIntegrable).mul_continuousOn ?_
  refine (continuousOn_const.div continuousOn_id ?_).pow 3
  intro x hx
  have : min a b ≤ x := (Set.mem_uIcc.mp hx).elim (fun h => (min_le_left _ _).trans h.1)
    (fun h => (min_le_right _ _).trans h.1)
  have : 0 < x := lt_of_lt_of_le (lt_min ha hb) this
  exact this.ne'

/-- Head: `∫_2^{B'} Dpt ≤ 2.00002 δ X √X` for `B' ≤ X`. Unit task393. -/
theorem int_Dpt_head {δ X B' : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hX : 10 ^ 13 ≤ X)
    (hB : 2 ≤ B') (hBX : B' ≤ X) :
    ∫ y in (2 : ℝ)..B', Dpt δ y ≤ 200002 / 100000 * δ * (X * √X) := by
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hX2 : 2 ≤ X := le_trans (by norm_num) hX
  have hδs : δ ≤ 1 / 100000 := hδ1.trans (by norm_num)
  have h1 : ∫ y in (2 : ℝ)..B', Dpt δ y ≤ ∫ y in (1 : ℝ)..X, Dpt δ y :=
    intervalIntegral.integral_mono_interval (by norm_num) hB hBX
      (ae_restrict_of_forall_mem measurableSet_Ioc
        (fun y hy => Dpt_nonneg hδ.le (by linarith [hy.1]))) (Dpt_ii hδ 1 X)
  have h2 := intD_le hX2 hδ (by linarith)
  have h3 : fpt ((1 + δ) * X) ≤ 2 * √((1 + δ) * X) :=
    fpt_le_two_sqrt (by nlinarith)
  have h4 : √((1 + δ) * X) ≤ 100001 / 100000 * √X := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hX0.le]
    nlinarith
  have h5 : δ * X * fpt ((1 + δ) * X) ≤ δ * X * (2 * (100001 / 100000 * √X)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h6 : δ * X * (2 * (100001 / 100000 * √X)) = 200002 / 100000 * δ * (X * √X) := by ring
  linarith

/-- Tail: `∫_X^B Dpt (X/y)^3 ≤ 6.00004 δ X √X`. Unit task393. -/
theorem int_Dpt_tail {δ X B : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hX : 10 ^ 13 ≤ X)
    (hXB : X ≤ B) :
    ∫ y in X..B, Dpt δ y * (X / y) ^ 3 ≤ 600004 / 100000 * δ * (X * √X) := by
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hB0 : 0 < B := lt_of_lt_of_le hX0 hXB
  have hk : 0 < 1 + δ := by linarith
  have hδs : δ ≤ 1 / 100000 := hδ1.trans (by norm_num)
  have hs : 0 < √X := Real.sqrt_pos.mpr hX0
  have hC : 0 < X * √X := mul_pos hX0 hs
  have hkX : 0 < (1 + δ) * X := mul_pos hk hX0
  have hkB : 0 < (1 + δ) * B := mul_pos hk hB0
  have hXkX : X ≤ (1 + δ) * X := by nlinarith
  have hBkB : B ≤ (1 + δ) * B := by nlinarith
  -- the shifted piece
  have hA : ∫ y in X..B, fpt ((1 + δ) * y) * (X / y) ^ 3
      = (1 + δ) ^ 2 * ∫ u in (1 + δ) * X..(1 + δ) * B, fpt u * (X / u) ^ 3 := by
    have e : ∫ y in X..B, fpt ((1 + δ) * y) * (X / y) ^ 3
        = ∫ y in X..B, (1 + δ) ^ 3 * (fpt ((1 + δ) * y) * (X / ((1 + δ) * y)) ^ 3) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hy0 : 0 < y := by
        rw [Set.uIcc_of_le hXB] at hy
        exact lt_of_lt_of_le hX0 hy.1
      show fpt ((1 + δ) * y) * (X / y) ^ 3
        = (1 + δ) ^ 3 * (fpt ((1 + δ) * y) * (X / ((1 + δ) * y)) ^ 3)
      field_simp
    rw [e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun u => fpt u * (X / u) ^ 3) (ne_of_gt hk),
      smul_eq_mul, ← mul_assoc]
    have e3 : (1 + δ) ^ 3 * (1 + δ)⁻¹ = (1 + δ) ^ 2 := by field_simp
    rw [e3]
  have i1 : IntervalIntegrable (fun y => fpt ((1 + δ) * y) * (X / y) ^ 3) volume X B := by
    have hm : Monotone fun t => fpt ((1 + δ) * t) := fun u v huv => fpt_mono (by nlinarith)
    refine (hm.intervalIntegrable).mul_continuousOn ?_
    refine (continuousOn_const.div continuousOn_id ?_).pow 3
    intro x hx
    rw [Set.uIcc_of_le hXB] at hx
    exact (lt_of_lt_of_le hX0 hx.1).ne'
  have hsplit : ∫ y in X..B, Dpt δ y * (X / y) ^ 3
      = (∫ y in X..B, fpt ((1 + δ) * y) * (X / y) ^ 3) - ∫ y in X..B, fpt y * (X / y) ^ 3 := by
    rw [← intervalIntegral.integral_sub i1 (F_ii X hX0 hB0)]
    apply intervalIntegral.integral_congr
    intro y _
    show Dpt δ y * (X / y) ^ 3 = fpt ((1 + δ) * y) * (X / y) ^ 3 - fpt y * (X / y) ^ 3
    unfold Dpt; ring
  -- interval bookkeeping
  have s1 : (∫ u in X..(1 + δ) * X, fpt u * (X / u) ^ 3)
      + (∫ u in (1 + δ) * X..(1 + δ) * B, fpt u * (X / u) ^ 3)
      = ∫ u in X..(1 + δ) * B, fpt u * (X / u) ^ 3 :=
    intervalIntegral.integral_add_adjacent_intervals (F_ii X hX0 hkX) (F_ii X hkX hkB)
  have s2 : (∫ u in X..B, fpt u * (X / u) ^ 3)
      + (∫ u in B..(1 + δ) * B, fpt u * (X / u) ^ 3)
      = ∫ u in X..(1 + δ) * B, fpt u * (X / u) ^ 3 :=
    intervalIntegral.integral_add_adjacent_intervals (F_ii X hX0 hB0) (F_ii X hB0 hkB)
  have h3 : 0 ≤ ∫ u in X..(1 + δ) * X, fpt u * (X / u) ^ 3 :=
    intervalIntegral.integral_nonneg hXkX (fun u hu =>
      mul_nonneg (fpt_nonneg u) (pow_nonneg (div_nonneg hX0.le (hX0.le.trans hu.1)) 3))
  -- I1
  have hI1 : ∫ u in X..B, fpt u * (X / u) ^ 3 ≤ 2 * (X * √X) := by
    have hnot : (0 : ℝ) ∉ Set.uIcc X B := by
      rw [Set.uIcc_of_le hXB]; intro h; linarith [h.1]
    have hg : IntervalIntegrable (fun u : ℝ => 2 * X ^ 2 * √X * u ^ (-2 : ℝ)) volume X B :=
      (intervalIntegral.intervalIntegrable_rpow (Or.inr hnot)).const_mul _
    have hle : ∫ u in X..B, fpt u * (X / u) ^ 3 ≤ ∫ u in X..B, 2 * X ^ 2 * √X * u ^ (-2 : ℝ) := by
      apply intervalIntegral.integral_mono_on hXB (F_ii X hX0 hB0) hg
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hX0 hu.1
      have := F_le hX hu.1
      rw [Real.rpow_neg hu0.le, Real.rpow_two]
      exact this
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by norm_num, hnot⟩)] at hle
    have e : (-2 : ℝ) + 1 = -1 := by norm_num
    rw [e, Real.rpow_neg_one, Real.rpow_neg_one] at hle
    have hBi : 0 ≤ B⁻¹ := inv_nonneg.mpr hB0.le
    have e2 : 2 * X ^ 2 * √X * ((B⁻¹ - X⁻¹) / -1)
        = 2 * (X * √X) - 2 * X ^ 2 * √X * B⁻¹ := by
      field_simp; ring
    have : 0 ≤ 2 * X ^ 2 * √X * B⁻¹ := by positivity
    linarith
  -- I2
  have hI2 : ∫ u in B..(1 + δ) * B, fpt u * (X / u) ^ 3 ≤ 2 * δ * (X * √X) := by
    have hle : ∫ u in B..(1 + δ) * B, fpt u * (X / u) ^ 3
        ≤ ∫ u in B..(1 + δ) * B, 2 * X ^ 2 * √X * (B ^ 2)⁻¹ := by
      apply intervalIntegral.integral_mono_on hBkB (F_ii X hB0 hkB) intervalIntegrable_const
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hB0 hu.1
      have h1 := F_le hX (hXB.trans hu.1)
      have h2 : (u ^ 2)⁻¹ ≤ (B ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ hB0.le hu.1 2)
      have h3 : 2 * X ^ 2 * √X * (u ^ 2)⁻¹ ≤ 2 * X ^ 2 * √X * (B ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    have e : ((1 + δ) * B - B) * (2 * X ^ 2 * √X * (B ^ 2)⁻¹) = 2 * δ * (X * √X) * (X / B) := by
      field_simp; ring
    have hXB1 : X / B ≤ 1 := (div_le_one hB0).mpr hXB
    have : 2 * δ * (X * √X) * (X / B) ≤ 2 * δ * (X * √X) :=
      mul_le_of_le_one_right (by positivity) hXB1
    linarith
  have hI10 : 0 ≤ ∫ u in X..B, fpt u * (X / u) ^ 3 :=
    intervalIntegral.integral_nonneg hXB (fun u hu =>
      mul_nonneg (fpt_nonneg u) (pow_nonneg (div_nonneg hX0.le (hX0.le.trans hu.1)) 3))
  have hI20 : 0 ≤ ∫ u in B..(1 + δ) * B, fpt u * (X / u) ^ 3 :=
    intervalIntegral.integral_nonneg hBkB (fun u hu =>
      mul_nonneg (fpt_nonneg u) (pow_nonneg (div_nonneg hX0.le (hB0.le.trans hu.1)) 3))
  rw [hsplit, hA]
  set I1 := ∫ u in X..B, fpt u * (X / u) ^ 3 with hI1def
  set I2 := ∫ u in B..(1 + δ) * B, fpt u * (X / u) ^ 3 with hI2def
  set I3 := ∫ u in X..(1 + δ) * X, fpt u * (X / u) ^ 3 with hI3def
  set J := ∫ u in (1 + δ) * X..(1 + δ) * B, fpt u * (X / u) ^ 3 with hJdef
  have hJ : J ≤ I1 + I2 := by linarith
  have hk2 : (1 + δ) ^ 2 ≤ 1 + 200001 / 100000 * δ := by nlinarith
  have hk20 : 0 ≤ (1 + δ) ^ 2 := by positivity
  have hk21 : (1 + δ) ^ 2 ≤ 100001 / 50000 / 2 + 1 / 100000 := by nlinarith
  have a1 : (1 + δ) ^ 2 * J ≤ (1 + δ) ^ 2 * (I1 + I2) := mul_le_mul_of_nonneg_left hJ hk20
  have a2 : ((1 + δ) ^ 2 - 1) * I1 ≤ 200001 / 100000 * δ * (2 * (X * √X)) :=
    mul_le_mul (by linarith) hI1 hI10 (by positivity)
  have a3 : (1 + δ) ^ 2 * I2 ≤ (100001 / 50000 / 2 + 1 / 100000) * (2 * δ * (X * √X)) :=
    mul_le_mul hk21 hI2 hI20 (by norm_num)
  have hδC : 0 ≤ δ * (X * √X) := by positivity
  nlinarith

/-- The first moment of `Dpt` against `min(1, (X/y)^3)` on `(2, B]`. Unit task393. -/
theorem int_Dpt_g_le {δ X B : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hX : 10 ^ 13 ≤ X)
    (hB : 2 ≤ B) :
    ∫ y in (2:ℝ)..B, Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3)
      ≤ 801 / 100 * δ * (X * √X) := by
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hX2 : 2 ≤ X := le_trans (by norm_num) hX
  have hs : 0 < √X := Real.sqrt_pos.mpr hX0
  have hδC : 0 ≤ δ * (X * √X) := by positivity
  have hhead : ∀ B' : ℝ, 2 ≤ B' → B' ≤ X →
      ∫ y in (2:ℝ)..B', Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3) = ∫ y in (2:ℝ)..B', Dpt δ y := by
    intro B' h2 hBX
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le h2] at hy
    show Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3) = Dpt δ y
    simp only [hy.2.trans hBX, ↓reduceIte, mul_one]
  rcases le_or_gt B X with hBX | hBX
  · rw [hhead B hB hBX]
    have := int_Dpt_head hδ hδ1 hX hB hBX
    linarith
  · have hXB : X ≤ B := hBX.le
    have e1 : Set.EqOn (Dpt δ) (fun y => Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3))
        (Set.uIoc 2 X) := by
      intro y hy
      rw [Set.uIoc_of_le hX2] at hy
      show Dpt δ y = Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3)
      simp only [hy.2, ↓reduceIte, mul_one]
    have e2 : Set.EqOn (fun y => Dpt δ y * (X / y) ^ 3)
        (fun y => Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3)) (Set.uIoc X B) := by
      intro y hy
      rw [Set.uIoc_of_le hXB] at hy
      show Dpt δ y * (X / y) ^ 3 = Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3)
      simp only [not_le.mpr hy.1, ↓reduceIte]
    have iT : IntervalIntegrable (fun y => Dpt δ y * (X / y) ^ 3) volume X B := by
      refine (Dpt_ii hδ X B).mul_continuousOn ?_
      refine (continuousOn_const.div continuousOn_id ?_).pow 3
      intro x hx
      rw [Set.uIcc_of_le hXB] at hx
      exact (lt_of_lt_of_le hX0 hx.1).ne'
    have i1 := (intervalIntegrable_congr e1).mp (Dpt_ii hδ 2 X)
    have i2 := (intervalIntegrable_congr e2).mp iT
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, hhead X hX2 le_rfl]
    have et : ∫ y in X..B, Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3)
        = ∫ y in X..B, Dpt δ y * (X / y) ^ 3 := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le hXB] at hy
      show Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3) = Dpt δ y * (X / y) ^ 3
      split_ifs with h
      · have : y = X := le_antisymm h hy.1
        rw [this, div_self hX0.ne']; norm_num
      · rfl
    rw [et]
    have h1 := int_Dpt_head hδ hδ1 hX hX2 le_rfl
    have h2 := int_Dpt_tail hδ hδ1 hX hXB
    linarith

/-! ### `∫_0^∞ y W(y/X) dy ≤ X²` -/

/-- `y W(y/X) = y` for `y ≤ X`. Unit task393. -/
theorem y_W_eq_left {X y : ℝ} (hX : 0 < X) (hy : y ≤ X) : y * W (y / X) = y := by
  have h1 : y / X ≤ 1 := (div_le_one hX).mpr hy
  unfold W
  simp only [h1, ↓reduceIte, mul_one]

/-- `y W(y/X) = X⁴ y^(-3)` for `y > X`. Unit task393. -/
theorem y_W_eq_right {X y : ℝ} (hX : 0 < X) (hy : X < y) :
    y * W (y / X) = X ^ 4 * y ^ (-3 : ℝ) := by
  have hy0 : 0 < y := hX.trans hy
  have h1 : ¬ (y / X ≤ 1) := by rw [div_le_one hX]; exact not_le.mpr hy
  unfold W
  simp only [h1, ↓reduceIte]
  rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hy0.le,
    Real.rpow_natCast]
  field_simp

theorem integrableOn_y_W_Ioc {X : ℝ} (hX : 0 < X) :
    IntegrableOn (fun y : ℝ => y * W (y / X)) (Ioc 0 X) := by
  have h : IntegrableOn (fun y : ℝ => y) (Ioc 0 X) := continuous_id.integrableOn_Ioc
  exact h.congr_fun (fun y hy => (y_W_eq_left hX hy.2).symm) measurableSet_Ioc

theorem integrableOn_y_W_Ioi {X : ℝ} (hX : 0 < X) :
    IntegrableOn (fun y : ℝ => y * W (y / X)) (Ioi X) := by
  have h : IntegrableOn (fun y : ℝ => X ^ 4 * y ^ (-3 : ℝ)) (Ioi X) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hX).const_mul _
  exact h.congr_fun (fun y hy => (y_W_eq_right hX hy).symm) measurableSet_Ioi

/-- `y ↦ y W(y/X)` is integrable on `(0, ∞)`. Unit task393. -/
theorem integrableOn_y_W {X : ℝ} (hX : 0 < X) :
    IntegrableOn (fun y : ℝ => y * W (y / X)) (Ioi 0) := by
  have h := (integrableOn_y_W_Ioc hX).union (integrableOn_y_W_Ioi hX)
  rwa [Set.Ioc_union_Ioi_eq_Ioi hX.le] at h

/-- `∫_0^∞ y W(y/X) dy ≤ X²`; the value is `X²`. Unit task393. -/
theorem integral_y_W_le {X : ℝ} (hX : 0 < X) : ∫ y in Ioi (0:ℝ), y * W (y / X) ≤ X ^ 2 := by
  have hd : Disjoint (Ioc (0 : ℝ) X) (Ioi X) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact absurd hu.2 (not_le.mpr hu')
  rw [← Set.Ioc_union_Ioi_eq_Ioi hX.le,
    MeasureTheory.setIntegral_union hd measurableSet_Ioi (integrableOn_y_W_Ioc hX)
      (integrableOn_y_W_Ioi hX),
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun y hy => y_W_eq_left hX hy.2),
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => y_W_eq_right hX hy),
    ← intervalIntegral.integral_of_le hX.le, integral_id, MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) hX]
  have e : (-3 : ℝ) + 1 = -2 := by norm_num
  rw [e, Real.rpow_neg hX.le, Real.rpow_two]
  have e2 : X ^ 4 * (-(X ^ 2)⁻¹ / -2) = X ^ 2 / 2 := by
    field_simp
  rw [e2]
  nlinarith [sq_nonneg X]

end LeanLab.Task393
