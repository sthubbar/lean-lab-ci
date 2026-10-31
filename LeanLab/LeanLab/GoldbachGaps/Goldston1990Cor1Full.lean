import LeanLab.GoldbachGaps.Goldston1990Cor1

/-!
# Goldston 1990, Corollary 1 under RH on the printed interval `[N, N + K]`

Lab proof, unit U-6307, CLOUD 20261020T1017Z-cloud40, P0030. AI wrote this file. Known
mathematics, Goldston 1990, Corollary 1, display 7.

The centred results of `Goldston1990Thm6RH`, `Goldston1990Sec5` and `Goldston1990Cor1` are
redone along an arbitrary sequence of centres `c(i) → ∞`, `fejer_asymp_seq`, `rsum_asymp_seq`,
`rsumr_asymp_seq`, so that the centre may move with `K`. Then `corollary1_rh_full`: under RH,
for `K = K(N)` with `log² N = o(K)` and `64 K² ≤ N`,
`Σ_{N ≤ n ≤ N + K} r(n) ~ K N / log² N`, the conclusion of the lab's cited `Corollary1` with its
`J(N, K) = o(K² N)` hypothesis replaced by RH, PROVED CONDITIONAL ON RiemannHypothesis only. The
range `64 K² ≤ N` is narrower than the paper's `K ≤ N/log³ N`. Binary Goldbach is OPEN.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset Filter

/-- The RH bound on `J`, pointwise: `J(N, K) ≤ 30 C (log² N / K) K² N`. -/
theorem jg_pointwise (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N K : ℕ, 1 ≤ K → K * K ≤ N →
    1 ≤ Real.log N → Jg N K ≤ 30 * C * (Real.log N ^ 2 / K) * ((K : ℝ) ^ 2 * N) := by
  obtain ⟨C, hC, hj⟩ := jg_rh_b hRH
  refine ⟨C, hC, fun N K hK1 hKN hl1 => ?_⟩
  have hN1 : 1 ≤ N := le_trans hK1 (le_trans (Nat.le_mul_self K) hKN)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hb := hj N K hK1 hKN
  set l := Real.log N with hl
  set ℓ := Real.log (N / K) + 3 with hℓ
  have hKNr : (K : ℝ) ≤ N := by
    have : (K : ℝ) * K ≤ N := by exact_mod_cast hKN
    nlinarith
  have hl0 : 0 ≤ Real.log (N / K) := Real.log_nonneg (by rw [le_div_iff₀ hK0]; linarith)
  have hl1' : Real.log (N / K) ≤ l := Real.log_le_log (by positivity) (div_le_self hN0.le hK1r)
  have hsK : 1 ≤ Real.sqrt K := Real.one_le_sqrt.mpr hK1r
  have t1 : (K : ℝ) * N * ℓ ^ 2 ≤ 16 * l ^ 2 * ((K : ℝ) * N) := by
    have : ℓ ≤ 4 * l := by linarith
    have : ℓ ^ 2 ≤ 16 * l ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (K : ℝ) * N)]
  have t2 : (N : ℝ) * ((l + 2) ^ 2 / Real.sqrt K) ≤ 9 * l ^ 2 * N := by
    have h1 : (l + 2) ^ 2 / Real.sqrt K ≤ (l + 2) ^ 2 := div_le_self (by positivity) hsK
    have h2 : (l + 2) ^ 2 ≤ 9 * l ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hN0.le]
  have e : 30 * C * (l ^ 2 / K) * ((K : ℝ) ^ 2 * N) = 30 * C * (l ^ 2 * ((K : ℝ) * N)) := by
    field_simp
  rw [e]
  calc Jg N K ≤ C * ((K : ℝ) * N * ℓ ^ 2 + N * ((l + 2) ^ 2 / Real.sqrt K)) := hb
    _ ≤ C * (16 * l ^ 2 * ((K : ℝ) * N) + 9 * l ^ 2 * N) := by gcongr
    _ ≤ C * (16 * l ^ 2 * ((K : ℝ) * N) + 9 * l ^ 2 * ((K : ℝ) * N)) := by
        gcongr
        nlinarith
    _ ≤ 30 * C * (l ^ 2 * ((K : ℝ) * N)) := by
        have : 0 ≤ C * (l ^ 2 * ((K : ℝ) * N)) := by positivity
        nlinarith

/-- `√N ≤ N / log³ N` for all large `N`, pointwise. -/
lemma sqrt_le_eventually : ∃ N1 : ℕ, ∀ N : ℕ, N1 ≤ N → Real.sqrt N ≤ N / Real.log N ^ 3 :=
  eventually_atTop.1 eventually_sqrt_le

/-- **The Fejér asymptotic along a sequence of centres**, under RH. -/
theorem fejer_asymp_seq (hRH : RiemannHypothesis) (c K : ℕ → ℕ) (hc : Tendsto c atTop atTop)
    (hlog : Tendsto (fun i : ℕ => Real.log (c i) ^ 2 / K i) atTop (nhds 0))
    (hK : ∀ᶠ i : ℕ in atTop, 1 ≤ K i ∧ K i * K i ≤ c i) :
    Tendsto (fun i : ℕ => fejer (c i) (K i) / ((K i : ℝ) ^ 2 * c i)) atTop (nhds 1) := by
  obtain ⟨C, hC, hT⟩ := theorem6_proved
  obtain ⟨CJ, hCJ, hJ⟩ := jg_pointwise hRH
  obtain ⟨N1, hN1⟩ := sqrt_le_eventually
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N0, hN0⟩ := hT (δ / 3) (by positivity)
  set η := min (δ / (3 * C)) (δ / (3 * (30 * CJ + 1))) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have e2 : ∀ᶠ i : ℕ in atTop, Real.log (c i) ^ 2 / K i < η :=
    hlog.eventually (Iio_mem_nhds hη0)
  have tc : Tendsto (fun i => ((c i : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hc
  have e3 : ∀ᶠ i : ℕ in atTop, 1 ≤ Real.log (c i) :=
    (Real.tendsto_log_atTop.comp tc).eventually_ge_atTop 1
  have e5 : ∀ᶠ i : ℕ in atTop, max N0 N1 ≤ c i := hc.eventually_ge_atTop _
  obtain ⟨M, hM⟩ := eventually_atTop.1 (e2.and (e3.and (hK.and e5)))
  refine ⟨M, fun i hi => ?_⟩
  obtain ⟨h2, h3, ⟨h4a, h4b⟩, h5⟩ := hM i hi
  set N := c i with hNdef
  set k := K i with hkdef
  have hkpos : (0 : ℝ) < k := by exact_mod_cast h4a
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := le_trans h4a (le_trans (Nat.le_mul_self _) h4b)
    exact_mod_cast this
  have hrange : (k : ℝ) ≤ N / Real.log N ^ 3 := by
    refine le_trans ?_ (hN1 N (le_trans (le_max_right _ _) h5))
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have : ((k * k : ℕ) : ℝ) ≤ N := by exact_mod_cast h4b
    push_cast at this; nlinarith
  have hT' := hN0 N (le_trans (le_max_left _ _) h5) k h4a hrange
  have hD : 0 < (k : ℝ) ^ 2 * N := by positivity
  rw [Real.dist_eq]
  have hrw : fejer N k / ((k : ℝ) ^ 2 * N) - 1 = (fejer N k - (k : ℝ) ^ 2 * N) / ((k : ℝ) ^ 2 * N) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hD, div_lt_iff₀ hD]
  have hl2 : 1 ≤ Real.log N ^ 2 := by nlinarith
  have hlk : Real.log N ^ 2 / k < η := h2
  have hJb := hJ N k h4a h4b h3
  have hJ' : Jg N k < δ / 3 * ((k : ℝ) ^ 2 * N) := by
    have : 30 * CJ * (Real.log N ^ 2 / k) ≤ 30 * CJ * η :=
      mul_le_mul_of_nonneg_left hlk.le (by positivity)
    have h3' : 30 * CJ * η < δ / 3 := by
      have : η ≤ δ / (3 * (30 * CJ + 1)) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith
    nlinarith
  have hCK : C < δ / 3 * k := by
    have h1 : Real.log N ^ 2 / k < δ / (3 * C) := lt_of_lt_of_le hlk (min_le_left _ _)
    rw [div_lt_iff₀ hkpos] at h1
    have : 1 < δ / (3 * C) * k := by linarith
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)] at this
    linarith
  have hCKN : C * k * N < δ / 3 * ((k : ℝ) ^ 2 * N) := by
    have := mul_lt_mul_of_pos_right hCK (show (0 : ℝ) < k * N by positivity)
    nlinarith
  have hε : δ / 3 * (k : ℝ) ^ 2 * N = δ / 3 * ((k : ℝ) ^ 2 * N) := by ring
  rw [hε] at hT'
  linarith

/-- **Section 5 along a sequence of centres**, under RH. -/
theorem rsum_asymp_seq (hRH : RiemannHypothesis) (c K : ℕ → ℕ) (hc : Tendsto c atTop atTop)
    (hlog : Tendsto (fun i : ℕ => Real.log (c i) ^ 2 / K i) atTop (nhds 0))
    (hK : ∀ᶠ i : ℕ in atTop, 1 ≤ K i ∧ 4 * (K i * K i) ≤ c i) :
    Tendsto (fun i : ℕ => Rsum (c i) (K i) / (2 * K i * c i)) atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set m : ℕ := ⌈2 / δ⌉₊ + 2 with hm
  have hm2 : 2 / δ ≤ (m : ℝ) := by
    have := Nat.le_ceil (2 / δ); rw [hm]; push_cast; linarith
  have hm1 : (2 : ℕ) ≤ m := by omega
  set η : ℝ := δ / (10 * m) with hη
  have hη0 : 0 < η := by positivity
  have tc : Tendsto (fun i => ((c i : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hc
  have eL : ∀ᶠ i : ℕ in atTop, 1 ≤ Real.log (c i) :=
    (Real.tendsto_log_atTop.comp tc).eventually_ge_atTop 1
  have eS : ∀ᶠ i : ℕ in atTop, Real.log (c i) ^ 2 / K i < 1 / (2 * m) :=
    hlog.eventually (Iio_mem_nhds (by positivity))
  have eBig : ∀ᶠ i : ℕ in atTop, 2 * m ≤ K i := by
    filter_upwards [eL, eS, hK] with i hL hS hKi
    have hKpos : (0 : ℝ) < K i := by exact_mod_cast hKi.1
    rw [div_lt_iff₀ hKpos] at hS
    have hl2 : 1 ≤ Real.log (c i) ^ 2 := by nlinarith
    have : (2 * m : ℝ) < K i := by
      have h2 : 1 < 1 / (2 * m) * (K i : ℝ) := by linarith
      rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ (by positivity)] at h2
      linarith
    exact_mod_cast this.le
  have hK1 : ∀ᶠ i : ℕ in atTop, 1 ≤ K i ∧ K i * K i ≤ c i := by
    filter_upwards [hK] with i h; exact ⟨h.1, by nlinarith [h.2]⟩
  set Kp : ℕ → ℕ := fun i => K i + K i / m with hKp
  set Km : ℕ → ℕ := fun i => K i - K i / m with hKm
  have hdiv : ∀ i, K i / m ≤ K i / 2 := fun i => Nat.div_le_div_left hm1 (by norm_num)
  have tp : Tendsto (fun i : ℕ => Real.log (c i) ^ 2 / Kp i) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
    · filter_upwards with i; positivity
    · filter_upwards [hK] with i h
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast h.1)
      simp only [hKp]; push_cast; linarith [(Nat.cast_nonneg (K i / m) : (0 : ℝ) ≤ _)]
  have tm : Tendsto (fun i : ℕ => Real.log (c i) ^ 2 / Km i) atTop (nhds 0) := by
    have h2 : Tendsto (fun i : ℕ => 2 * (Real.log (c i) ^ 2 / K i)) atTop (nhds 0) := by
      simpa using hlog.const_mul 2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    · filter_upwards with i; positivity
    · filter_upwards [hK, eBig] with i h hb
      have hKm2 : (K i : ℝ) / 2 ≤ Km i := by
        simp only [hKm]
        have := hdiv i
        have h4 : K i - K i / m ≥ K i - K i / 2 := by omega
        have h5 : ((K i - K i / 2 : ℕ) : ℝ) * 2 ≥ K i := by
          have : (K i - K i / 2) * 2 ≥ K i := by omega
          exact_mod_cast this
        have h6 : ((K i - K i / m : ℕ) : ℝ) ≥ ((K i - K i / 2 : ℕ) : ℝ) := by exact_mod_cast h4
        linarith
      have hKpos : (0 : ℝ) < K i := by exact_mod_cast h.1
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) hKpos]
      have : 0 ≤ Real.log (c i) ^ 2 := sq_nonneg _
      nlinarith
  have aK := fejer_asymp_seq hRH c K hc hlog hK1
  have aP := fejer_asymp_seq hRH c Kp hc tp (by
    filter_upwards [hK] with i h
    refine ⟨le_trans h.1 (Nat.le_add_right _ _), ?_⟩
    have : Kp i ≤ 2 * K i := by simp only [hKp]; have := hdiv i; omega
    nlinarith)
  have aM := fejer_asymp_seq hRH c Km hc tm (by
    filter_upwards [hK, eBig] with i h hb
    refine ⟨?_, ?_⟩
    · simp only [hKm]; have := hdiv i; omega
    · have : Km i ≤ K i := Nat.sub_le _ _
      nlinarith [h.2])
  rw [Metric.tendsto_atTop] at aK aP aM
  obtain ⟨A1, hA1⟩ := aK η hη0
  obtain ⟨A2, hA2⟩ := aP η hη0
  obtain ⟨A3, hA3⟩ := aM η hη0
  obtain ⟨A4, hA4⟩ := eventually_atTop.1 (hK.and eBig)
  refine ⟨max (max A1 A2) (max A3 A4), fun i hi => ?_⟩
  have hi1 : A1 ≤ i := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hi
  have hi2 : A2 ≤ i := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hi
  have hi3 : A3 ≤ i := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hi
  have hi4 : A4 ≤ i := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hi
  obtain ⟨⟨hKN1, hKN4⟩, hb⟩ := hA4 i hi4
  set N := c i with hNdef
  set h := K i / m with hhdef
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := by nlinarith
    exact_mod_cast this
  have hkpos : (0 : ℝ) < K i := by exact_mod_cast hKN1
  have hhm : h * m ≤ K i := Nat.div_mul_le_self _ _
  have hmh : K i < (h + 1) * m := by
    have := Nat.lt_div_mul_add (a := K i) (show 0 < m by omega)
    rw [← hhdef] at this
    calc K i < h * m + m := this
      _ = (h + 1) * m := by ring
  have hh1 : 1 ≤ h := by
    rw [hhdef]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hh1
  have hhkR : (h : ℝ) * m ≤ K i := by exact_mod_cast hhm
  have hkhR : (K i : ℝ) ≤ 2 * m * h := by
    have : K i ≤ 2 * m * h := by nlinarith
    exact_mod_cast this
  have hU := fejer_diff_upper N (K i) h
  have hL := fejer_diff_lower N (K i) h (by rw [hhdef]; exact Nat.div_le_self _ _)
  have hD0 : (0 : ℝ) < (K i : ℝ) ^ 2 * N := by positivity
  have hF0 := abs_sub_le_of_dist hD0 (hA1 i hi1)
  have hFp := abs_sub_le_of_dist (show (0 : ℝ) < (Kp i : ℝ) ^ 2 * N by
    have : (0 : ℝ) < Kp i := by simp only [hKp]; push_cast; positivity
    positivity) (hA2 i hi2)
  have hFm := abs_sub_le_of_dist (show (0 : ℝ) < (Km i : ℝ) ^ 2 * N by
    have : (0 : ℝ) < Km i := by
      have : 1 ≤ Km i := by simp only [hKm]; have := hdiv i; omega
      exact_mod_cast this
    positivity) (hA3 i hi3)
  have eKp : (Kp i : ℝ) = K i + h := by simp only [hKp]; push_cast; rfl
  have eKm : (Km i : ℝ) = K i - h := by
    simp only [hKm]; rw [Nat.cast_sub (Nat.div_le_self _ _)]
  rw [eKp] at hFp
  rw [eKm] at hFm
  have hfp : fejer N (Kp i) = fejer N (K i + h) := rfl
  have hfm : fejer N (Km i) = fejer N (K i - h) := rfl
  rw [hfp] at hFp
  rw [hfm] at hFm
  apply dist_div_lt (by positivity)
  exact diff_algebra hkpos hhpos hNpos hδ hm2 (by exact_mod_cast (show 1 ≤ m by omega)) hhkR hkhR
    hU hL hF0 hFp hFm

set_option maxHeartbeats 2000000 in
/-- **Corollary 1, centred form, along a sequence of centres**, under RH. -/
theorem rsumr_asymp_seq (hRH : RiemannHypothesis) (c K : ℕ → ℕ) (hc : Tendsto c atTop atTop)
    (hlog : Tendsto (fun i : ℕ => Real.log (c i) ^ 2 / K i) atTop (nhds 0))
    (hK : ∀ᶠ i : ℕ in atTop, 1 ≤ K i ∧ 4 * (K i * K i) ≤ c i) :
    Tendsto (fun i : ℕ => rsumr (c i) (K i) / (2 * K i * c i / Real.log (c i) ^ 2)) atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro δ0 hδ0
  set δ := min δ0 1 with hδdef
  have hδ : 0 < δ := lt_min hδ0 one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set ε := min (1 / 5 : ℝ) (δ / 10) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε5 : ε ≤ 1 / 5 := min_le_left _ _
  have hεδ : ε ≤ δ / 10 := min_le_right _ _
  have aR := rsum_asymp_seq hRH c K hc hlog hK
  rw [Metric.tendsto_atTop] at aR
  obtain ⟨A1, hA1⟩ := aR (δ / 4) (by positivity)
  have tc : Tendsto (fun i => ((c i : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hc
  have tL := Real.tendsto_log_atTop.comp tc
  have eL : ∀ᶠ i : ℕ in atTop, max (max 1 (64 / ε ^ 2)) (max (8 / δ) (24 / δ)) ≤ Real.log (c i) :=
    tL.eventually_ge_atTop _
  have t4 : Tendsto (fun i : ℕ => Real.log (c i) ^ 4 / (1 * ((c i : ℕ) : ℝ) + 0)) atTop (nhds 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp tc
  have e4 : ∀ᶠ i : ℕ in atTop, Real.log (c i) ^ 4 / (1 * ((c i : ℕ) : ℝ) + 0) < δ / 24 :=
    t4.eventually (Iio_mem_nhds (by positivity))
  have eN : ∀ᶠ i : ℕ in atTop, A1 ≤ i := eventually_ge_atTop A1
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eL.and (e4.and (eN.and hK)))
  refine ⟨M, fun i hiM => ?_⟩
  obtain ⟨hLb, h4, hNA, hK1, hK4⟩ := hM i hiM
  set N := c i with hNdef
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLb
  have hL64 : 64 / ε ^ 2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLb
  have hL8 : 8 / δ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLb
  have hL24 : 24 / δ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLb
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := by nlinarith
    exact_mod_cast this
  have hkpos : (0 : ℝ) < K i := by exact_mod_cast hK1
  have hKN : (K i : ℝ) ≤ N := by
    have : K i ≤ N := by nlinarith
    exact_mod_cast this
  have hL0 : 0 < L := by linarith
  -- the R sum
  have hR := hA1 i hNA
  have hD : (0 : ℝ) < 2 * K i * N := by positivity
  rw [Real.dist_eq, abs_lt] at hR
  have hRlo : (1 - δ / 4) * (2 * K i * N) ≤ Rsum N (K i) := by
    have := hR.1; rw [lt_sub_iff_add_lt, lt_div_iff₀ hD] at this; nlinarith
  have hRhi : Rsum N (K i) ≤ (1 + δ / 4) * (2 * K i * N) := by
    have := hR.2; rw [sub_lt_iff_lt_add, div_lt_iff₀ hD] at this; nlinarith
  have hδδ : δ ≤ δ0 := min_le_left _ _
  have hL24' : 24 ≤ δ * L := by rw [div_le_iff₀ hδ] at hL24; linarith
  have hR0 : 0 ≤ Rsum N (K i) := le_trans (by nlinarith) hRlo
  rw [show rsumr N (K i) / (2 * K i * N / L ^ 2) = rsumr N (K i) * L ^ 2 / (2 * K i * N) by
    field_simp]
  rw [Real.dist_eq, abs_lt]
  constructor
  · -- lower bound
    have hlog2 : Real.log ((N : ℝ) + K i) ≤ L + 1 := by
      have h2N : (N : ℝ) + K i ≤ 2 * N := by linarith
      have := Real.log_le_log (by positivity) h2N
      rw [Real.log_mul (by norm_num) hNpos.ne'] at this
      have : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    have hlog0 : 0 < Real.log ((N : ℝ) + K i) := by
      have hN1 : (1 : ℝ) < N := by
        by_contra h; push_neg at h
        have : L ≤ 0 := by rw [hLdef]; exact Real.log_nonpos hNpos.le h
        linarith
      exact Real.log_pos (by linarith)
    have hge := rsumr_ge N (K i)
    have := cor1_lower hδ hδ1 hL1 hL24' hD hRlo hge hlog0 hlog2
    linarith
  · -- upper bound
    set y : ℝ := N / L ^ 4 with hydef
    have hL4 : 0 < L ^ 4 := by positivity
    have h4' : L ^ 4 / N < δ / 24 := by simpa using h4
    have h4'' : L ^ 4 < δ / 24 * N := by rwa [div_lt_iff₀ hNpos] at h4'
    have hy2 : 2 ≤ y := by
      rw [hydef, le_div_iff₀ hL4]; nlinarith
    have hy1 : 1 < y := by linarith
    have hlogy : (1 - ε) * L ≤ Real.log y := by
      rw [hydef, Real.log_div hNpos.ne' hL4.ne', Real.log_pow]
      have hll : Real.log L ≤ 2 * Real.sqrt L := LeanLab.GoldbachAverage.log_le_two_sqrt hL0
      have hL64' : 64 ≤ ε ^ 2 * L := by rw [div_le_iff₀ (by positivity)] at hL64; linarith
      have hsq : 8 ≤ ε * Real.sqrt L := by
        have hsL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
        have h0 : 0 ≤ ε * Real.sqrt L := by positivity
        nlinarith
      have hsL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
      have : 8 * Real.sqrt L ≤ ε * L := by nlinarith [Real.sqrt_nonneg L]
      push_cast
      linarith
    have hle := rsumr_le N (K i) hy1
    have hE : (2 * K i + 1) * (2 * (y + 1)) * L ^ 2 ≤ δ / 4 * (2 * K i * N) :=
      cor1_E (by exact_mod_cast hK1) hNpos hL1 hL24' hδ
        (by rw [hydef, div_mul_cancel₀ _ hL4.ne']) (by linarith)
    have := cor1_upper hδ hδ1 hε hε5 hεδ hL0 hlogy hD hRhi hR0 hle hE
    linarith


lemma rg_le_self (n : ℕ) : (rg n : ℝ) ≤ n := by
  have : rg n ≤ n := by
    unfold rg; exact (card_filter_le _ _).trans (by rw [card_range])
  exact_mod_cast this

/-- The interval sum against the centred one: `Σ_{N ≤ n ≤ N + K} r(n) = rsumr (N + w) w + tail`,
`w = ⌊K/2⌋`, with `0 ≤ tail ≤ N + K`. -/
lemma icc_eq_rsumr (N K : ℕ) : ∃ t : ℝ, 0 ≤ t ∧ t ≤ N + K ∧
    ∑ n ∈ Icc N (N + K), (rg n : ℝ) = rsumr (N + K / 2) (K / 2) + t := by
  set w := K / 2 with hw
  have hIcc : ∑ n ∈ Icc N (N + K), (rg n : ℝ) = ∑ j ∈ range (K + 1), (rg (N + j) : ℝ) := by
    have : Icc N (N + K) = Ico N (N + K + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [this, sum_Ico_eq_sum_range, show N + K + 1 - N = K + 1 by omega]
  have hr : rsumr (N + w) w = ∑ j ∈ range (2 * w + 1), (rg (N + j) : ℝ) := by
    unfold rsumr; apply sum_congr rfl; intro j _; congr 2; omega
  refine ⟨∑ j ∈ Ico (2 * w + 1) (K + 1), (rg (N + j) : ℝ), sum_nonneg fun _ _ => Nat.cast_nonneg _,
    ?_, ?_⟩
  · have hcard : (Ico (2 * w + 1) (K + 1)).card ≤ 1 := by rw [Nat.card_Ico]; omega
    calc ∑ j ∈ Ico (2 * w + 1) (K + 1), (rg (N + j) : ℝ) ≤ ∑ _j ∈ Ico (2 * w + 1) (K + 1), ((N : ℝ) + K) := by
          apply sum_le_sum; intro j hj
          have := mem_Ico.mp hj
          have h1 := rg_le_self (N + j)
          have : ((N + j : ℕ) : ℝ) ≤ N + K := by push_cast; exact_mod_cast (show N + j ≤ N + K by omega)
          linarith
      _ ≤ (N : ℝ) + K := by
          rw [sum_const, nsmul_eq_mul]
          have : ((Ico (2 * w + 1) (K + 1)).card : ℝ) ≤ 1 := by exact_mod_cast hcard
          nlinarith [(by positivity : (0 : ℝ) ≤ (N : ℝ) + K)]
  · rw [hIcc, hr, ← sum_range_add_sum_Ico _ (show 2 * w + 1 ≤ K + 1 by omega)]

/-- **Goldston's Corollary 1 under RH, on `[N, N + K]`.** For `K = K(N)` with `log² N = o(K)` and
`64 K² ≤ N`, `Σ_{N ≤ n ≤ N + K} r(n) ~ K N / log² N`. PROVED CONDITIONAL ON RiemannHypothesis
only. -/
theorem corollary1_rh_full (hRH : RiemannHypothesis) (K : ℕ → ℕ)
    (hlog : Tendsto (fun N : ℕ => Real.log N ^ 2 / K N) atTop (nhds 0))
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ 64 * (K N * K N) ≤ N) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) / ((K N : ℝ) * N / Real.log N ^ 2))
      atTop (nhds 1) := by
  set c : ℕ → ℕ := fun N => N + K N / 2 with hcdef
  set w : ℕ → ℕ := fun N => K N / 2 with hwdef
  have tN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have eL : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N := (Real.tendsto_log_atTop.comp tN).eventually_ge_atTop 1
  have eK3 : ∀ᶠ N : ℕ in atTop, 3 ≤ K N := by
    filter_upwards [eL, hlog.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)), hK] with N hL hS hKN
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast hKN.1
    rw [div_lt_iff₀ hKpos] at hS
    have : (3 : ℝ) < K N := by nlinarith
    exact_mod_cast this.le
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_add_right N _) tendsto_id
  -- K/N → 0
  have hKN0 : Tendsto (fun N : ℕ => (K N : ℝ) / N) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
    · filter_upwards with N; positivity
    · filter_upwards [hK, eL] with N h hL
      have hk : (1 : ℝ) ≤ K N := by exact_mod_cast h.1
      have hN : (64 : ℝ) * (K N * K N) ≤ N := by exact_mod_cast h.2
      have hNpos : (0 : ℝ) < N := by nlinarith
      rw [div_le_div_iff₀ hNpos (by linarith)]
      have hl2 : (1 : ℝ) ≤ Real.log N ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hl2 hNpos.le]
  -- log c ≤ log N + K/N, and log c ≥ log N
  have hlogc : ∀ᶠ N : ℕ in atTop, Real.log N ≤ Real.log (c N) ∧
      Real.log (c N) ≤ Real.log N * (1 + (K N : ℝ) / N) := by
    filter_upwards [hK, eL] with N h hL
    have hk : (1 : ℝ) ≤ K N := by exact_mod_cast h.1
    have hN : (64 : ℝ) * (K N * K N) ≤ N := by exact_mod_cast h.2
    have hNpos : (0 : ℝ) < N := by nlinarith
    have hcN : (c N : ℝ) = N + ((K N / 2 : ℕ) : ℝ) := by simp [hcdef]
    have hw0 : (0 : ℝ) ≤ ((K N / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hwK : ((K N / 2 : ℕ) : ℝ) ≤ K N := by exact_mod_cast Nat.div_le_self _ _
    constructor
    · rw [hcN]; exact Real.log_le_log hNpos (by linarith)
    · rw [hcN]
      have h1 : Real.log (N + ((K N / 2 : ℕ) : ℝ)) ≤ Real.log N + ((K N / 2 : ℕ) : ℝ) / N := by
        have : (N : ℝ) + ((K N / 2 : ℕ) : ℝ) = N * (1 + ((K N / 2 : ℕ) : ℝ) / N) := by field_simp
        rw [this, Real.log_mul hNpos.ne' (by positivity)]
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + ((K N / 2 : ℕ) : ℝ) / N by positivity)
        linarith
      have h2 : ((K N / 2 : ℕ) : ℝ) / N ≤ Real.log N * ((K N : ℝ) / N) := by
        have : ((K N / 2 : ℕ) : ℝ) / N ≤ (K N : ℝ) / N := div_le_div_of_nonneg_right hwK hNpos.le
        have h0 : 0 ≤ (K N : ℝ) / N := by positivity
        nlinarith
      linarith
  -- hypotheses for the centred theorem at (c, w)
  have hw : ∀ᶠ N : ℕ in atTop, 1 ≤ w N ∧ 4 * (w N * w N) ≤ c N := by
    filter_upwards [hK, eK3] with N h h3
    refine ⟨by simp only [hwdef]; omega, ?_⟩
    simp only [hwdef, hcdef]
    have a : 2 * (K N / 2) ≤ K N := Nat.mul_div_le _ _
    have b := Nat.mul_le_mul a a
    have : 4 * (K N / 2 * (K N / 2)) = (2 * (K N / 2)) * (2 * (K N / 2)) := by ring
    have h2 := h.2
    have : K N * K N ≤ 64 * (K N * K N) := by omega
    omega
  have hlogw : Tendsto (fun N : ℕ => Real.log (c N) ^ 2 / w N) atTop (nhds 0) := by
    have h12 : Tendsto (fun N : ℕ => 12 * (Real.log N ^ 2 / K N)) atTop (nhds 0) := by
      simpa using hlog.const_mul 12
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h12
    · filter_upwards with N; positivity
    · filter_upwards [hK, eK3, hlogc, eL] with N h h3 hl hL
      have hk : (3 : ℝ) ≤ K N := by exact_mod_cast h3
      have hw3 : (K N : ℝ) / 3 ≤ w N := by
        simp only [hwdef]
        have : K N ≤ 3 * (K N / 2) := by omega
        have : (K N : ℝ) ≤ 3 * ((K N / 2 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have hN : (64 : ℝ) * (K N * K N) ≤ N := by exact_mod_cast h.2
      have hNpos : (0 : ℝ) < N := by nlinarith
      have hKN1 : (K N : ℝ) / N ≤ 1 := by rw [div_le_one hNpos]; nlinarith
      have hlc : Real.log (c N) ≤ 2 * Real.log N := by nlinarith [hl.2]
      have hlc0 : 0 ≤ Real.log (c N) := le_trans (by linarith) hl.1
      have hsq : Real.log (c N) ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
      have hwpos : (0 : ℝ) < w N := lt_of_lt_of_le (by positivity) hw3
      rw [div_le_iff₀ hwpos]
      have : 12 * (Real.log N ^ 2 / K N) * (K N / 3) = 4 * Real.log N ^ 2 := by
        field_simp; ring
      have hpos : 0 ≤ 12 * (Real.log N ^ 2 / K N) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hw3 hpos]
  have A := rsumr_asymp_seq hRH c w hc hlogw hw
  -- the three correction factors
  have B1 : Tendsto (fun N : ℕ => 2 * (w N : ℝ) / K N) atTop (nhds 1) := by
    have hinv : Tendsto (fun N : ℕ => 1 - 1 / (K N : ℝ)) atTop (nhds 1) := by
      have : Tendsto (fun N : ℕ => 1 / (K N : ℝ)) atTop (nhds 0) := by
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
        · filter_upwards with N; positivity
        · filter_upwards [eL] with N hL
          apply div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hinv tendsto_const_nhds
    · filter_upwards [eK3] with N h3
      have hk : (0 : ℝ) < K N := by exact_mod_cast (show 0 < K N by omega)
      rw [le_div_iff₀ hk]
      have : K N ≤ 2 * (K N / 2) + 1 := by omega
      have : (K N : ℝ) ≤ 2 * ((K N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
      simp only [hwdef]; rw [sub_mul, one_div_mul_cancel hk.ne']; linarith
    · filter_upwards [eK3] with N h3
      have hk : (0 : ℝ) < K N := by exact_mod_cast (show 0 < K N by omega)
      rw [div_le_one hk]
      have : 2 * (K N / 2) ≤ K N := Nat.mul_div_le _ _
      simp only [hwdef]; exact_mod_cast this
  have B2 : Tendsto (fun N : ℕ => (c N : ℝ) / N) atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hKN0)
    · filter_upwards [hK] with N h
      have hN : (64 : ℝ) * (K N * K N) ≤ N := by exact_mod_cast h.2
      have hk : (1 : ℝ) ≤ K N := by exact_mod_cast h.1
      have hNpos : (0 : ℝ) < N := by nlinarith
      rw [le_div_iff₀ hNpos, one_mul]; simp only [hcdef]; push_cast; linarith [(Nat.cast_nonneg (K N / 2) : (0 : ℝ) ≤ _)]
    · filter_upwards [hK] with N h
      have hN : (64 : ℝ) * (K N * K N) ≤ N := by exact_mod_cast h.2
      have hk : (1 : ℝ) ≤ K N := by exact_mod_cast h.1
      have hNpos : (0 : ℝ) < N := by nlinarith
      rw [div_le_iff₀ hNpos, add_mul, one_mul, div_mul_cancel₀ _ hNpos.ne']
      simp only [hcdef]; push_cast
      have : ((K N / 2 : ℕ) : ℝ) ≤ K N := by exact_mod_cast Nat.div_le_self _ _
      linarith
  have B3 : Tendsto (fun N : ℕ => (Real.log N / Real.log (c N)) ^ 2) atTop (nhds 1) := by
    have hlo : Tendsto (fun N : ℕ => 1 / (1 + (K N : ℝ) / N)) atTop (nhds 1) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hKN0).inv₀ (by norm_num)
    have h1 : Tendsto (fun N : ℕ => Real.log N / Real.log (c N)) atTop (nhds 1) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
      · filter_upwards [hlogc, eL] with N hl hL
        have hpos : 0 < Real.log (c N) := lt_of_lt_of_le (by linarith) hl.1
        rw [le_div_iff₀ hpos]
        have h0 : 0 < 1 + (K N : ℝ) / N := by positivity
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h0]; linarith [hl.2]
      · filter_upwards [hlogc, eL] with N hl hL
        have hpos : 0 < Real.log (c N) := lt_of_lt_of_le (by linarith) hl.1
        rw [div_le_one hpos]; exact hl.1
    simpa using h1.pow 2
  -- the tail
  have T0 : Tendsto (fun N : ℕ => ((N : ℝ) + K N) / ((K N : ℝ) * N / Real.log N ^ 2)) atTop (nhds 0) := by
    have h2 : Tendsto (fun N : ℕ => 2 * (Real.log N ^ 2 / K N)) atTop (nhds 0) := by
      simpa using hlog.const_mul 2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    · filter_upwards [hK, eL] with N h hL
      have hk : (1 : ℝ) ≤ K N := by exact_mod_cast h.1
      have hN : (64 : ℝ) * (K N * K N) ≤ N := by exact_mod_cast h.2
      have hNpos : (0 : ℝ) < N := by nlinarith
      positivity
    · filter_upwards [hK, eL] with N h hL
      have hk : (1 : ℝ) ≤ K N := by exact_mod_cast h.1
      have hN : (64 : ℝ) * (K N * K N) ≤ N := by exact_mod_cast h.2
      have hNpos : (0 : ℝ) < N := by nlinarith
      have hKN : (K N : ℝ) ≤ N := by nlinarith
      rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
      have : 2 * (Real.log N ^ 2 / K N) * (K N * N) = 2 * Real.log N ^ 2 * N := by field_simp
      rw [this]; nlinarith [sq_nonneg (Real.log N)]
  -- assemble
  have key : ∀ᶠ N : ℕ in atTop, ∃ t : ℝ, 0 ≤ t ∧ t ≤ N + K N ∧
      (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) / ((K N : ℝ) * N / Real.log N ^ 2) =
        rsumr (c N) (w N) / (2 * w N * c N / Real.log (c N) ^ 2) *
          (2 * (w N : ℝ) / K N * ((c N : ℝ) / N) * (Real.log N / Real.log (c N)) ^ 2) +
          t / ((K N : ℝ) * N / Real.log N ^ 2) := by
    filter_upwards [hK, hw, eL, hlogc] with N h hwN hL hl
    obtain ⟨t, ht0, ht1, ht⟩ := icc_eq_rsumr N (K N)
    refine ⟨t, ht0, ht1, ?_⟩
    have hk : (0 : ℝ) < K N := by exact_mod_cast (show 0 < K N by omega)
    have hwpos : (0 : ℝ) < w N := by exact_mod_cast (show 0 < w N by omega)
    have hN : (64 : ℝ) * (K N * K N) ≤ N := by exact_mod_cast h.2
    have hNpos : (0 : ℝ) < N := by nlinarith
    have hcpos : (0 : ℝ) < c N := by simp only [hcdef]; push_cast; positivity
    have hlc : 0 < Real.log (c N) := lt_of_lt_of_le (by linarith) hl.1
    have hLpos : 0 < Real.log N := by linarith
    rw [ht]
    simp only [hcdef, hwdef] at *
    field_simp
  have lim : Tendsto (fun N : ℕ => rsumr (c N) (w N) / (2 * w N * c N / Real.log (c N) ^ 2) *
      (2 * (w N : ℝ) / K N * ((c N : ℝ) / N) * (Real.log N / Real.log (c N)) ^ 2)) atTop (nhds 1) := by
    simpa using A.mul ((B1.mul B2).mul B3)
  rw [Metric.tendsto_atTop] at lim T0 ⊢
  intro δ hδ
  obtain ⟨M1, hM1⟩ := lim (δ / 2) (by positivity)
  obtain ⟨M2, hM2⟩ := T0 (δ / 2) (by positivity)
  obtain ⟨M3, hM3⟩ := eventually_atTop.1 (key.and hK)
  refine ⟨max (max M1 M2) M3, fun N hN => ?_⟩
  obtain ⟨⟨t, ht0, ht1, ht⟩, h⟩ := hM3 N (le_trans (le_max_right _ _) hN)
  have hk : (1 : ℝ) ≤ K N := by exact_mod_cast h.1
  have hNN : (64 : ℝ) * (K N * K N) ≤ N := by exact_mod_cast h.2
  have hNpos : (0 : ℝ) < N := by nlinarith
  have a1 := hM1 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have a2 := hM2 N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  rw [ht]
  rw [Real.dist_eq] at a1 a2 ⊢
  have hD : 0 ≤ (K N : ℝ) * N / Real.log N ^ 2 := by positivity
  have htD : t / ((K N : ℝ) * N / Real.log N ^ 2) ≤ ((N : ℝ) + K N) / ((K N : ℝ) * N / Real.log N ^ 2) :=
    div_le_div_of_nonneg_right ht1 hD
  have ht0' : 0 ≤ t / ((K N : ℝ) * N / Real.log N ^ 2) := div_nonneg ht0 hD
  rw [sub_zero, abs_lt] at a2
  rw [abs_lt] at a1 ⊢
  constructor <;> linarith [a1.1, a1.2, a2.2]

end LeanLab.GoldbachGaps.Goldston1990
