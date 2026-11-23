import LeanLab.Zhan1991.HighFree1122
import LeanLab.Zhan1991.ZeroWindowFinite1122

/-!
P0068 Zhan 1991, page 269, the density part of the high range of (3.19), "by (2.4)", PROVED from
(2.4) of Lemma 4. With HighFree1122 this gives the whole high range `5/6 ≤ β ≤ 1` of (3.19)
CONDITIONAL ON the cited Lemma 4 display (2.4) and Lemma 5 only. It closes the LEAF
`highDensity_of_24` of SPLIT_display319_high_1122 by a separate proof, without editing that file.
burst-20261122, session S80. AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real Filter Asymptotics

/-- The three growth facts in `L = log N` the page 269 estimate uses, free of L functions:
`log 24 + c₂ log L ≤ L/48`, `c₂ log L ≤ L^{4/5}` and `L^{B+1+c₀'} ≤ exp(c₀ L^{1/5}/60)` for large `L`. -/
def AsympHigh : Prop :=
  ∀ c0 c2 c0' B : ℝ, 0 < c0 → 0 < c2 → 0 ≤ c0' → 0 < B → ∃ L0 : ℝ, ∀ L : ℝ, L0 ≤ L →
    Real.log 24 + c2 * Real.log L ≤ L / 48 ∧ c2 * Real.log L ≤ L ^ (4 / 5 : ℝ) ∧
      L ^ (B + 1 + c0') ≤ Real.exp (c0 * L ^ (1 / 5 : ℝ) / 60)

/-- Page 269, with `x = N^{1/8}`: `T ≤ 2x⁶` and `H ≤ 20x³`. PROVED. -/
theorem window_x_bounds269 (N : ℕ) (A lam : ℝ) (q : ℕ) (c1 c2 c3 c7 : ℝ) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (hc7 : 0 ≤ c7) (hc3 : c1 + c2 + c7 ≤ c3) (hN : (4096 : ℝ) ≤ N)
    (hL : 1 ≤ Real.log N) (hA : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A) (hAN : A ≤ N)
    (hq : 1 ≤ q) (hqL : (q : ℝ) ≤ Real.log N ^ c2)
    (hlam : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))) :
    T269 N A lam q c7 ≤ 2 * ((N : ℝ) ^ (1 / 8 : ℝ)) ^ 6 ∧
      H269 N A lam ≤ 20 * ((N : ℝ) ^ (1 / 8 : ℝ)) ^ 3 := by
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  set x := (N : ℝ) ^ (1 / 8 : ℝ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0 _
  have hx8 : x ^ 8 = N := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hP : (N : ℝ) ^ (5 / 8 : ℝ) = x ^ 5 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hx2 : 8 ≤ x ^ 2 := by
    by_contra h; push Not at h
    have : (x ^ 2) ^ 4 < 8 ^ 4 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
    have : x ^ 8 < 4096 := by nlinarith
    linarith
  have hx5pos : 0 < x ^ 5 := by
    have : 0 < x := by nlinarith
    positivity
  have hLc3 : 1 ≤ L ^ c3 := Real.one_le_rpow hL (by linarith)
  have hA0 : 0 < A := by nlinarith [hP ▸ hA]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsq : Real.sqrt q ≤ L ^ c2 := by
    refine le_trans ?_ hqL
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  obtain ⟨_, hH⟩ := H269_bounds N A lam q c1 hc1 hL hA0 hAN hq hlam
  have hT := T269_bound N A lam q c1 c7 hc1 hL hA0 hAN hq hlam
  -- powers of L
  have hc3' : 0 ≤ c3 := by linarith
  have hA2 : x ^ 10 * L ^ (c1 + c2 + c7) ≤ A ^ 2 := by
    have h1 : L ^ (c1 + c2 + c7) ≤ L ^ c3 := Real.rpow_le_rpow_of_exponent_le hL hc3
    have h2 : x ^ 5 * L ^ (c1 + c2 + c7) ≤ A := by
      rw [← hP]; exact (mul_le_mul_of_nonneg_left h1 (by rw [hP]; exact hx5pos.le)).trans hA
    have h3 : x ^ 5 ≤ x ^ 5 * L ^ (c1 + c2 + c7) :=
      le_mul_of_one_le_right hx5pos.le (Real.one_le_rpow hL (by linarith))
    calc x ^ 10 * L ^ (c1 + c2 + c7) = x ^ 5 * (x ^ 5 * L ^ (c1 + c2 + c7)) := by ring
      _ ≤ A * A := mul_le_mul (h3.trans h2) h2 (by positivity) hA0.le
      _ = A ^ 2 := by ring
  have hTb : T269 N A lam q c7 ≤ 2 * x ^ 6 := by
    have hLsum : L ^ c2 * L ^ c1 * L ^ c7 = L ^ (c1 + c2 + c7) := by
      rw [Real.rpow_add hL0, Real.rpow_add hL0]; ring
    have hpos : 0 < L ^ (c1 + c2 + c7) := Real.rpow_pos_of_pos hL0 _
    calc T269 N A lam q c7 ≤ 2 * Real.sqrt q * ((N : ℝ) ^ 2 * L ^ c1 / A ^ 2) * L ^ c7 := hT
      _ ≤ 2 * L ^ c2 * ((N : ℝ) ^ 2 * L ^ c1 / A ^ 2) * L ^ c7 := by
          gcongr
      _ = 2 * (N : ℝ) ^ 2 * (L ^ c2 * L ^ c1 * L ^ c7) / A ^ 2 := by ring
      _ = 2 * x ^ 16 * L ^ (c1 + c2 + c7) / A ^ 2 := by rw [hLsum, ← hx8]; ring
      _ ≤ 2 * x ^ 16 * L ^ (c1 + c2 + c7) / (x ^ 10 * L ^ (c1 + c2 + c7)) := by
          gcongr
      _ = 2 * x ^ 6 := by
          have : x ^ 10 ≠ 0 := by positivity
          field_simp
  have hHb : H269 N A lam ≤ 20 * x ^ 3 := by
    have h1 : L ^ c1 ≤ L ^ c3 := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have hLc1 : 0 < L ^ c1 := Real.rpow_pos_of_pos hL0 _
    have h2 : x ^ 5 * L ^ c1 ≤ A := by
      rw [← hP]; exact (mul_le_mul_of_nonneg_left h1 (by rw [hP]; exact hx5pos.le)).trans hA
    calc H269 N A lam ≤ 20 * N * L ^ c1 / A := hH
      _ ≤ 20 * N * L ^ c1 / (x ^ 5 * L ^ c1) := by gcongr
      _ = 20 * x ^ 3 := by rw [← hx8]; field_simp
  exact ⟨hTb, hHb⟩

set_option maxHeartbeats 1600000 in
/-- Page 269, "by (2.4)": enlarge the window to `H' = 20x³ + 2x² + 2 ≥ |T₁|^{1/3}`, apply (2.4),
`N^{β-1} (qH')^{12/5 (1-β)} ≤ exp(-(1-β)L/20)`, and below `beta5` this is at most
`exp(-c₀ L^{1/5}/60)`, which beats `L^{-B-1-c₀'}`. PROVED, CONDITIONAL ON `AsympHigh`. -/
theorem highDensity_of_24_asymp (h24 : Lemma4Eq24) (hAs : AsympHigh) (c0 : ℝ) (hc0 : 0 < c0) :
    HighDensityPart c0 := by
  obtain ⟨c0', hc0', K24, h24'⟩ := h24
  intro c1 c2 B c7 hc1 hc2 hB hc7
  obtain ⟨L0, hL0⟩ := hAs c0 c2 c0' B hc0 hc2 hc0'.le hB
  refine ⟨c1 + c2 + c7 + 1, by linarith, |K24|, max (max 4096 (Real.exp L0)) (Real.exp 1), ?_⟩
  intro N A α lam a q _ hN hA hAN hcond hq hlam β T1 hβ0 hβ1 hT1
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hN4 : (4096 : ℝ) ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNL0 : L0 ≤ Real.log N := by
    have := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
    simpa using Real.log_le_log (Real.exp_pos L0) this
  obtain ⟨hasA, hasB, hasC⟩ := hL0 (Real.log N) hNL0
  have hq1 : 1 ≤ q := hcond.2.2.2.1
  obtain ⟨hTx, hHx⟩ := window_x_bounds269 N A lam q c1 c2 (c1 + c2 + c7 + 1) c7 hc1.le hc2.le
    hc7.le (by linarith) hN4 hL1 hA hAN hq1 hq hcond.2.2.1
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  set x := (N : ℝ) ^ (1 / 8 : ℝ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0.le _
  have hx8 : x ^ 8 = N := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hx1 : 1 ≤ x := by
    by_contra h; push Not at h
    have : x ^ 8 < 1 := pow_lt_one₀ hx0 h (by norm_num)
    linarith
  have hxpos : 0 < x := by linarith
  have hlogx : Real.log x = L / 8 := by
    rw [hx, Real.log_rpow hN0]; ring
  -- enlarged window
  set H' := 20 * x ^ 3 + 2 * x ^ 2 + 2 with hH'
  clear_value H' x L
  have hHH' : H269 N A lam ≤ H' := by nlinarith
  have hH'2 : 2 ≤ H' := by nlinarith
  have hT0 : 0 ≤ T269 N A lam q c7 := by
    unfold T269
    have : 0 < A := lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hN0 _)
      (Real.rpow_pos_of_pos hLpos _)) hA
    have := Real.rpow_nonneg hLpos.le c7
    have := Real.sqrt_nonneg (q : ℝ)
    positivity
  have hT1' : |T1| ^ (1 / 3 : ℝ) ≤ H' := by
    have h1 : |T1| ≤ (2 * x ^ 2) ^ 3 := by nlinarith
    have h2 : |T1| ^ (1 / 3 : ℝ) ≤ ((2 * x ^ 2) ^ 3) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg _) h1 (by norm_num)
    have h3 : ((2 * x ^ 2) ^ 3) ^ (1 / 3 : ℝ) = 2 * x ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    rw [h3] at h2
    nlinarith
  have hmono := zeroCountZ_mono_H_proof q β T1 (H269 N A lam) H' (by linarith) hHH'
  have hD0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
  have hlogN2 : 0 < Real.log ((N : ℝ) + 2) := Real.log_pos (by linarith)
  have hDpos : 0 < Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) :=
    add_pos_of_nonneg_of_pos hD0 (Real.rpow_pos_of_pos hlogN2 _)
  have hβle : β ≤ 1 := by
    have : beta5 c0 N q ≤ 1 := by
      unfold beta5; have := div_nonneg hc0.le hDpos.le; linarith
    linarith
  have hz := h24' q β T1 H' hH'2 hT1' hβ0 hβle
  have hu0 : c0 / (Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ)) < 1 - β := by
    unfold beta5 at hβ1; linarith
  -- size of q H'
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hLc2 : 0 < L ^ c2 := Real.rpow_pos_of_pos hLpos _
  have hH'x : H' ≤ 24 * x ^ 3 := by
    have h1 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
    have h2 : 1 ≤ x ^ 3 := one_le_pow₀ hx1
    rw [hH']; linarith
  have hqH0 : 0 < (q : ℝ) * H' := by positivity
  have hlogqH : Real.log ((q : ℝ) * H') ≤ 19 * L / 48 := by
    have h1 : (q : ℝ) * H' ≤ L ^ c2 * (24 * x ^ 3) := mul_le_mul hq hH'x (by positivity) hLc2.le
    have h2 := Real.log_le_log hqH0 h1
    have h3 : Real.log (L ^ c2 * (24 * x ^ 3)) = c2 * Real.log L + Real.log 24 + 3 * (L / 8) := by
      rw [Real.log_mul hLc2.ne' (by positivity), Real.log_rpow hLpos,
        Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlogx]
      push_cast; ring
    linarith
  have hlogqH0 : 0 ≤ Real.log ((q : ℝ) * H') :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1' (by linarith))
  -- the power saving
  have hsave : (N : ℝ) ^ (β - 1) * ((q : ℝ) * H') ^ (12 / 5 * (1 - β)) ≤
      Real.exp (-((1 - β) * L / 20)) := by
    have hu : 0 ≤ 1 - β := by linarith
    have := mul_le_mul_of_nonneg_left hlogqH (by positivity : (0 : ℝ) ≤ 12 / 5 * (1 - β))
    have key : L * (β - 1) + Real.log ((q : ℝ) * H') * (12 / 5 * (1 - β)) ≤
        -((1 - β) * L / 20) := by linear_combination this
    rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos hqH0, ← Real.exp_add, ← hLdef]
    exact Real.exp_le_exp.mpr key
  -- the exponent from Lemma 5's threshold
  have hDle : Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) ≤ 3 * L ^ (4 / 5 : ℝ) := by
    have h1 : Real.log q ≤ c2 * Real.log L := by
      have := Real.log_le_log (by linarith) hq
      rwa [Real.log_rpow hLpos] at this
    have h2 : Real.log ((N : ℝ) + 2) ≤ 2 * L := by
      have : (N : ℝ) + 2 ≤ (N : ℝ) ^ 2 := by nlinarith
      have := Real.log_le_log (by linarith) this
      rw [Real.log_pow] at this; push_cast at this; linarith
    have h3 : Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) ≤ (2 * L) ^ (4 / 5 : ℝ) :=
      Real.rpow_le_rpow hlogN2.le h2 (by norm_num)
    have h4 : (2 * L) ^ (4 / 5 : ℝ) ≤ 2 * L ^ (4 / 5 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hLpos.le]
      have : (2 : ℝ) ^ (4 / 5 : ℝ) ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rw [Real.rpow_one] at this
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hLpos.le _)
    linarith
  have hL45 : 0 < L ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hsplitL : L = L ^ (4 / 5 : ℝ) * L ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_add hLpos]; norm_num
  have hexp : c0 * L ^ (1 / 5 : ℝ) / 60 ≤ (1 - β) * L / 20 := by
    have h1 : c0 / (3 * L ^ (4 / 5 : ℝ)) ≤ 1 - β :=
      (div_le_div_of_nonneg_left hc0.le hDpos hDle).trans hu0.le
    rw [div_le_iff₀ (by positivity)] at h1
    have : c0 * L ^ (1 / 5 : ℝ) / 60 = c0 * L ^ (1 / 5 : ℝ) / 60 := rfl
    have hL15 : 0 ≤ L ^ (1 / 5 : ℝ) := Real.rpow_nonneg hLpos.le _
    calc c0 * L ^ (1 / 5 : ℝ) / 60 ≤ (1 - β) * (3 * L ^ (4 / 5 : ℝ)) * L ^ (1 / 5 : ℝ) / 60 := by
          gcongr
      _ = (1 - β) * (L ^ (4 / 5 : ℝ) * L ^ (1 / 5 : ℝ)) / 20 := by ring
      _ = (1 - β) * L / 20 := by rw [← hsplitL]
  have hsave2 : (N : ℝ) ^ (β - 1) * ((q : ℝ) * H') ^ (12 / 5 * (1 - β)) ≤
      Real.exp (-(c0 * L ^ (1 / 5 : ℝ) / 60)) :=
    hsave.trans (Real.exp_le_exp.mpr (by linarith))
  have hlogpow : Real.log ((q : ℝ) * H') ^ c0' ≤ L ^ c0' :=
    Real.rpow_le_rpow hlogqH0 (by linarith) hc0'.le
  have hNb : 0 ≤ (N : ℝ) ^ (β - 1) := Real.rpow_nonneg hN0.le _
  have hfinal : Real.exp (-(c0 * L ^ (1 / 5 : ℝ) / 60)) * L ^ c0' ≤ L ^ (-B - 1) := by
    have hE := Real.exp_pos (c0 * L ^ (1 / 5 : ℝ) / 60)
    rw [Real.exp_neg]
    have hsum : L ^ (B + 1 + c0') = L ^ (B + 1) * L ^ c0' := by rw [Real.rpow_add hLpos]
    have hinv : L ^ (-B - 1) = (L ^ (B + 1))⁻¹ := by
      rw [show (-B - 1 : ℝ) = -(B + 1) by ring, Real.rpow_neg hLpos.le]
    rw [hinv, inv_mul_eq_div, le_inv_comm₀ (by positivity) (by positivity), inv_div,
      le_div_iff₀ (by positivity)]
    calc L ^ (B + 1) * L ^ c0' = L ^ (B + 1 + c0') := hsum.symm
      _ ≤ _ := hasC
      _ = _ := by ring
  have hS0 : 0 ≤ ((q : ℝ) * H') ^ (12 / 5 * (1 - β)) := Real.rpow_nonneg hqH0.le _
  have hlog0 : 0 ≤ Real.log ((q : ℝ) * H') ^ c0' := Real.rpow_nonneg hlogqH0 _
  calc (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q
      ≤ (N : ℝ) ^ (β - 1) * (K24 * ((q : ℝ) * H') ^ (12 / 5 * (1 - β)) *
          Real.log ((q : ℝ) * H') ^ c0') :=
        mul_le_mul_of_nonneg_left (hmono.trans hz) hNb
    _ ≤ (N : ℝ) ^ (β - 1) * (|K24| * ((q : ℝ) * H') ^ (12 / 5 * (1 - β)) *
          Real.log ((q : ℝ) * H') ^ c0') := by
        gcongr
        exact le_abs_self _
    _ = |K24| * (((N : ℝ) ^ (β - 1) * ((q : ℝ) * H') ^ (12 / 5 * (1 - β))) *
          Real.log ((q : ℝ) * H') ^ c0') := by ring
    _ ≤ |K24| * (Real.exp (-(c0 * L ^ (1 / 5 : ℝ) / 60)) * L ^ c0') := by
        gcongr
    _ ≤ |K24| * L ^ (-B - 1) := by gcongr

/-- `AsympHigh` holds: logarithms are `o` of powers and powers are `o` of exponentials. PROVED. -/
theorem asympHigh_proof : AsympHigh := by
  intro c0 c2 c0' B hc0 hc2 _ _
  show ∃ L0 : ℝ, ∀ L : ℝ, L0 ≤ L →
    Real.log 24 + c2 * Real.log L ≤ L / 48 ∧ c2 * Real.log L ≤ L ^ (4 / 5 : ℝ) ∧
      L ^ (B + 1 + c0') ≤ Real.exp (c0 * L ^ (1 / 5 : ℝ) / 60) 
  have ha : ∀ᶠ L : ℝ in atTop, Real.log L ≤ 1 / (96 * c2) * L := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).bound
      (by positivity : (0 : ℝ) < 1 / (96 * c2))
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with L hL hL1
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
      abs_of_nonneg (by linarith)] at hL
    exact hL
  have hb : ∀ᶠ L : ℝ in atTop, Real.log L ≤ 1 / c2 * L ^ (4 / 5 : ℝ) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).bound
      (by positivity : (0 : ℝ) < 1 / c2)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with L hL hL1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hL
    exact hL
  have hc : ∀ᶠ L : ℝ in atTop, L ^ (B + 1 + c0') ≤ Real.exp (c0 * L ^ (1 / 5 : ℝ) / 60) := by
    have hy : ∀ᶠ y : ℝ in atTop, y ^ (5 * (B + 1 + c0')) ≤ Real.exp (c0 / 60 * y) := by
      have h := (isLittleO_rpow_exp_pos_mul_atTop (5 * (B + 1 + c0'))
        (by positivity : 0 < c0 / 60)).bound (by norm_num : (0 : ℝ) < 1)
      filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with y hy hy0
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hy0 _),
        abs_of_nonneg (Real.exp_pos _).le, one_mul] at hy
      exact hy
    have ht : Tendsto (fun L : ℝ => L ^ (1 / 5 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    filter_upwards [ht.eventually hy, eventually_ge_atTop (0 : ℝ)] with L hL hL0
    have e : (L ^ (1 / 5 : ℝ)) ^ (5 * (B + 1 + c0')) = L ^ (B + 1 + c0') := by
      rw [← Real.rpow_mul hL0]; congr 1; ring
    rw [e] at hL
    calc L ^ (B + 1 + c0') ≤ Real.exp (c0 / 60 * L ^ (1 / 5 : ℝ)) := hL
      _ = _ := by congr 1; ring
  have hd : ∀ᶠ L : ℝ in atTop, Real.log 24 ≤ L / 96 := by
    filter_upwards [eventually_ge_atTop (96 * Real.log 24)] with L hL
    linarith
  obtain ⟨L0, hL0⟩ := eventually_atTop.mp (ha.and (hb.and (hc.and hd)))
  refine ⟨L0, fun L hL => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hL0 L hL
  refine ⟨?_, ?_, h3⟩
  · have : c2 * Real.log L ≤ c2 * (1 / (96 * c2) * L) := mul_le_mul_of_nonneg_left h1 hc2.le
    have e : c2 * (1 / (96 * c2) * L) = L / 96 := by field_simp
    linarith
  · have : c2 * Real.log L ≤ c2 * (1 / c2 * L ^ (4 / 5 : ℝ)) := mul_le_mul_of_nonneg_left h2 hc2.le
    have e : c2 * (1 / c2 * L ^ (4 / 5 : ℝ)) = L ^ (4 / 5 : ℝ) := by field_simp
    linarith

/-- Page 269, "by (2.4)": the density part of the high range from (2.4). PROVED from
`Lemma4Eq24`. -/
theorem highDensity_of_24_proof (h24 : Lemma4Eq24) (c0 : ℝ) (hc0 : 0 < c0) :
    HighDensityPart c0 :=
  highDensity_of_24_asymp h24 asympHigh_proof c0 hc0

/-- Page 269, the high range `5/6 ≤ β ≤ 1` of (3.19), PROVED, CONDITIONAL ON the cited (2.4) of
Lemma 4 and Lemma 5 only. -/
theorem display319_high_of_cited (h24 : Lemma4Eq24) (h5 : Lemma5NoExc) :
    Display319On (5 / 6) 1 := by
  obtain ⟨c0, hc0, hfree⟩ := highFree_of_lemma5_proof h5
  exact display319_high_of_parts c0 hfree (highDensity_of_24_proof h24 c0 hc0)

end LeanLab.Zhan1991
