import LeanLab.Zhan1991.HighDensity1122

/-!
P0068 Zhan 1991, page 269, the low range `1/2 ≤ β ≤ 5/6` of display (3.19), "using (2.3) we get",
PROVED from (2.3) of Lemma 4. With HighDensity1122 this gives (3.19) and Theorem 3 CONDITIONAL
ON the four cited inputs only: Lemma 6 of reference 2, displays (2.3) and (2.4) of Lemma 4, and
Lemma 5. It closes the LEAF `display319_low_of_23` of SPLIT_theorem3_1122 by a separate proof,
without editing that file. burst-20261122, session S80.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real Filter Asymptotics

/-- The growth facts in `L` the low range uses, free of L functions: `log 24 ≤ δ log L`,
`L^k ≤ exp(L/8) = N^{1/8}` and `L ≥ 2` for large `L`. -/
def AsympLow : Prop :=
  ∀ δ k : ℝ, 0 < δ → ∃ L0 : ℝ, ∀ L : ℝ, L0 ≤ L →
    Real.log 24 ≤ δ * Real.log L ∧ L ^ k ≤ Real.exp (L / 8) ∧ 2 ≤ L

/-- `AsympLow` holds. PROVED. -/
theorem asympLow_proof : AsympLow := by
  intro δ k hδ
  have h1 : ∀ᶠ L : ℝ in atTop, Real.log 24 ≤ δ * Real.log L := by
    have := (Real.tendsto_log_atTop).eventually (eventually_ge_atTop (Real.log 24 / δ))
    filter_upwards [this] with L hL
    rw [div_le_iff₀ hδ] at hL; linarith
  have h2 : ∀ᶠ L : ℝ in atTop, L ^ k ≤ Real.exp (L / 8) := by
    have h := (isLittleO_rpow_exp_pos_mul_atTop k (by norm_num : (0 : ℝ) < 1 / 8)).bound
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with L hL hL0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL0 _),
      abs_of_nonneg (Real.exp_pos _).le, one_mul] at hL
    calc L ^ k ≤ Real.exp (1 / 8 * L) := hL
      _ = _ := by congr 1; ring
  obtain ⟨L0, hL0⟩ := eventually_atTop.mp (h1.and (h2.and (eventually_ge_atTop (2 : ℝ))))
  exact ⟨L0, fun L hL => hL0 L hL⟩

set_option maxHeartbeats 1600000 in
/-- Page 269, "For 1/2 ≤ β ≤ 5/6, using (2.3)": enlarge the window to `H' = H + 2x² + 2`, which
keeps the saving `H ≤ 20 x³ L^{c₁-c₃}`; with `c₃ = c₁ + c₂ + c₇ + 1 + δ`,
`N^{β-1} (qH')^{8/3 (1-β)} ≤ exp(4/9 (log 24 - δ log L)) = 24^{4/9} L^{-(217+B)}` since
`1 - β ≥ 1/6`, and `(log qH')^{216} ≤ L^{216}`. PROVED, CONDITIONAL ON `AsympLow`. -/
theorem display319_low_asymp (h23 : Lemma4Eq23) (hAs : AsympLow) :
    Display319On (1 / 2) (5 / 6) := by
  obtain ⟨K23, h23'⟩ := h23
  intro c1 c2 B c7 hc1 hc2 hB hc7
  set δ : ℝ := 9 * (217 + B) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  set c3 : ℝ := c1 + c2 + c7 + 1 + δ with hc3
  obtain ⟨L0, hL0⟩ := hAs δ (c3 - c1) hδ0
  refine ⟨c3, by rw [hc3]; linarith, |K23| * 24 ^ (4 / 9 : ℝ),
    max (max 4096 (Real.exp L0)) (Real.exp 1), ?_⟩
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
  obtain ⟨hTx, -⟩ := window_x_bounds269 N A lam q c1 c2 c3 c7 hc1.le hc2.le
    hc7.le (by rw [hc3]; linarith) hN4 hL1 hA hAN hq1 hq hcond.2.2.1
  have hN0 : (0 : ℝ) < N := by linarith
  have hA0 : 0 < A := lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hN0 _)
      (Real.rpow_pos_of_pos (by linarith) _)) hA
  obtain ⟨h10, hH⟩ := H269_bounds N A lam q c1 hc1.le hL1 hA0 hAN hq1 hcond.2.2.1
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  set x := (N : ℝ) ^ (1 / 8 : ℝ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0.le _
  have hx8 : x ^ 8 = N := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hP : (N : ℝ) ^ (5 / 8 : ℝ) = x ^ 5 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hx1 : 1 ≤ x := by
    by_contra h; push Not at h
    have : x ^ 8 < 1 := pow_lt_one₀ hx0 h (by norm_num)
    linarith
  have hxpos : 0 < x := by linarith
  have hlogx : Real.log x = L / 8 := by
    rw [hx, Real.log_rpow hN0]; ring
  have hxexp : x = Real.exp (L / 8) := by
    rw [← hlogx, Real.exp_log hxpos]
  clear_value x L
  -- H ≤ 20 x³ L^{c1 - c3}
  have hLc : 0 < L ^ (c1 - c3) := Real.rpow_pos_of_pos hLpos _
  have hHs : H269 N A lam ≤ 20 * x ^ 3 * L ^ (c1 - c3) := by
    have h1 : x ^ 5 * L ^ c3 ≤ A := by rw [← hP]; exact hA
    have hc3p : 0 < L ^ c3 := Real.rpow_pos_of_pos hLpos _
    have e : L ^ (c1 - c3) = L ^ c1 / L ^ c3 := Real.rpow_sub hLpos _ _
    calc H269 N A lam ≤ 20 * N * L ^ c1 / A := hH
      _ ≤ 20 * N * L ^ c1 / (x ^ 5 * L ^ c3) := by
          have : 0 < x ^ 5 * L ^ c3 := by positivity
          gcongr
      _ = 20 * x ^ 3 * L ^ (c1 - c3) := by
          rw [e, ← hx8]; field_simp
  -- absorb the x² term
  have hx2 : 2 * x ^ 2 + 2 ≤ 4 * x ^ 3 * L ^ (c1 - c3) := by
    have hk : L ^ (c3 - c1) ≤ x := by rw [hxexp]; exact hasB
    have hinv : L ^ (c1 - c3) * L ^ (c3 - c1) = 1 := by
      rw [← Real.rpow_add hLpos]; simp
    have hx2' : 1 ≤ x ^ 2 := one_le_pow₀ hx1
    have : x ^ 2 ≤ x ^ 3 * L ^ (c1 - c3) := by
      have := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ x ^ 2 * L ^ (c1 - c3))
      calc x ^ 2 = x ^ 2 * (L ^ (c1 - c3) * L ^ (c3 - c1)) := by rw [hinv, mul_one]
        _ = x ^ 2 * L ^ (c1 - c3) * L ^ (c3 - c1) := by ring
        _ ≤ x ^ 2 * L ^ (c1 - c3) * x := this
        _ = x ^ 3 * L ^ (c1 - c3) := by ring
    linarith
  set H' := H269 N A lam + 2 * x ^ 2 + 2 with hH'
  clear_value H'
  have hH'0 : 0 ≤ H269 N A lam := by linarith
  have hH'2 : 2 ≤ H' := by rw [hH']; nlinarith
  have hT1' : |T1| ^ (1 / 3 : ℝ) ≤ H' := by
    have h1 : |T1| ≤ (2 * x ^ 2) ^ 3 := by nlinarith
    have h2 : |T1| ^ (1 / 3 : ℝ) ≤ ((2 * x ^ 2) ^ 3) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg _) h1 (by norm_num)
    have h3 : ((2 * x ^ 2) ^ 3) ^ (1 / 3 : ℝ) = 2 * x ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    rw [h3] at h2
    rw [hH']; linarith
  have hmono := zeroCountZ_mono_H_proof q β T1 (H269 N A lam) H' (by linarith)
    (by rw [hH']; nlinarith)
  have hz := h23' q β T1 H' hH'2 hT1' hβ0 (by linarith)
  -- size of q H'
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hLc2 : 0 < L ^ c2 := Real.rpow_pos_of_pos hLpos _
  have hH'x : H' ≤ 24 * x ^ 3 * L ^ (c1 - c3) := by rw [hH']; linarith
  have hqH0 : 0 < (q : ℝ) * H' := by positivity
  have hlogqH : Real.log ((q : ℝ) * H') ≤ Real.log 24 - δ * Real.log L + 3 * (L / 8) := by
    have h1 : (q : ℝ) * H' ≤ L ^ c2 * (24 * x ^ 3 * L ^ (c1 - c3)) :=
      mul_le_mul hq hH'x (by positivity) hLc2.le
    have h2 := Real.log_le_log hqH0 h1
    have h3 : Real.log (L ^ c2 * (24 * x ^ 3 * L ^ (c1 - c3))) =
        Real.log 24 - (c7 + 1 + δ) * Real.log L + 3 * (L / 8) := by
      rw [Real.log_mul hLc2.ne' (by positivity), Real.log_rpow hLpos,
        Real.log_mul (by positivity) hLc.ne', Real.log_rpow hLpos,
        Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlogx, hc3]
      push_cast; ring
    have : 0 ≤ (c7 + 1) * Real.log L := mul_nonneg (by linarith) (Real.log_nonneg hL1)
    linarith
  have hlogqH0 : 0 ≤ Real.log ((q : ℝ) * H') :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1' (by linarith))
  have hlogqHL : Real.log ((q : ℝ) * H') ≤ L := by
    have : 0 ≤ δ * Real.log L := mul_nonneg hδ0.le (Real.log_nonneg hL1)
    linarith
  -- the power saving
  have hsave : (N : ℝ) ^ (β - 1) * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) ≤
      Real.exp (4 / 9 * (Real.log 24 - δ * Real.log L)) := by
    have hu : 1 / 6 ≤ 1 - β := by linarith
    have hneg : Real.log 24 - δ * Real.log L ≤ 0 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hlogqH (by positivity : (0 : ℝ) ≤ 8 / 3 * (1 - β))
    have h2 := mul_le_mul_of_nonpos_right hu hneg
    have key : L * (β - 1) + Real.log ((q : ℝ) * H') * (8 / 3 * (1 - β)) ≤
        4 / 9 * (Real.log 24 - δ * Real.log L) := by
      linear_combination h1 + 8 / 3 * h2
    rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos hqH0, ← Real.exp_add, ← hLdef]
    exact Real.exp_le_exp.mpr key
  have hexpval : Real.exp (4 / 9 * (Real.log 24 - δ * Real.log L)) =
      24 ^ (4 / 9 : ℝ) * L ^ (-(217 + B)) := by
    rw [show 4 / 9 * (Real.log 24 - δ * Real.log L) =
        Real.log 24 * (4 / 9) + Real.log L * (-(217 + B)) by rw [hδ]; ring,
      Real.exp_add, ← Real.rpow_def_of_pos (by norm_num), ← Real.rpow_def_of_pos hLpos]
  have hlogpow : Real.log ((q : ℝ) * H') ^ (216 : ℝ) ≤ L ^ (216 : ℝ) :=
    Real.rpow_le_rpow hlogqH0 hlogqHL (by norm_num)
  have hNb : 0 ≤ (N : ℝ) ^ (β - 1) := Real.rpow_nonneg hN0.le _
  have hpow : L ^ (-(217 + B)) * L ^ (216 : ℝ) = L ^ (-B - 1) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  have h24p : 0 ≤ (24 : ℝ) ^ (4 / 9 : ℝ) := by positivity
  calc (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q
      ≤ (N : ℝ) ^ (β - 1) * (K23 * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) *
          Real.log ((q : ℝ) * H') ^ (216 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hmono.trans hz) hNb
    _ ≤ (N : ℝ) ^ (β - 1) * (|K23| * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) *
          Real.log ((q : ℝ) * H') ^ (216 : ℝ)) := by
        have := Real.rpow_nonneg hqH0.le (8 / 3 * (1 - β))
        have := Real.rpow_nonneg hlogqH0 (216 : ℝ)
        gcongr
        exact le_abs_self _
    _ = |K23| * (((N : ℝ) ^ (β - 1) * ((q : ℝ) * H') ^ (8 / 3 * (1 - β))) *
          Real.log ((q : ℝ) * H') ^ (216 : ℝ)) := by ring
    _ ≤ |K23| * ((24 ^ (4 / 9 : ℝ) * L ^ (-(217 + B))) * L ^ (216 : ℝ)) := by
        rw [← hexpval]
        have := Real.rpow_nonneg hlogqH0 (216 : ℝ)
        gcongr
    _ = |K23| * 24 ^ (4 / 9 : ℝ) * L ^ (-B - 1) := by rw [← hpow]; ring

/-- Page 269, the low range of (3.19), PROVED from the cited (2.3) of Lemma 4. -/
theorem display319_low_of_cited (h23 : Lemma4Eq23) : Display319On (1 / 2) (5 / 6) :=
  display319_low_asymp h23 asympLow_proof

/-- Page 269, display (3.19) on `1/2 ≤ β ≤ 1`, PROVED, CONDITIONAL ON (2.3), (2.4) and Lemma 5. -/
theorem display319_of_cited (h23 : Lemma4Eq23) (h24 : Lemma4Eq24) (h5 : Lemma5NoExc) :
    Display319 :=
  display319_of_ranges (display319_low_of_cited h23) (display319_high_of_cited h24 h5)

/-- Theorem 3 of page 260, PROVED, CONDITIONAL ON the four cited inputs of its page 269 proof:
Lemma 6 of reference 2, displays (2.3) and (2.4) of Lemma 4, and Lemma 5. -/
theorem theorem3_of_cited (h6 : PanPanLemma6) (h23 : Lemma4Eq23) (h24 : Lemma4Eq24)
    (h5 : Lemma5NoExc) : Theorem3 :=
  theorem3_of_split h6 (display319_of_cited h23 h24 h5)

/-- Theorem 3 wired through the four cited LEAFs only. -/
theorem zhan_theorem3_cited_only : Theorem3 :=
  theorem3_of_cited panpan_lemma6_cited lemma4_eq23_cited lemma4_eq24_cited lemma5_cited

end LeanLab.Zhan1991
