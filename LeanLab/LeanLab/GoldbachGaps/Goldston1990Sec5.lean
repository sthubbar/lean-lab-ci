import LeanLab.GoldbachGaps.Goldston1990Thm6RH

/-!
# Goldston 1990, Section 5: the unweighted sum `Σ_{|n| ≤ K} R(N + n) ~ 2 K N` under RH

Lab proof, unit U-6302, CLOUD 20261020T1017Z-cloud40, P0030. AI wrote this file. Known
mathematics, Goldston 1990, Section 5, page 292.

Goldston takes differences of the Fejér sum `S(K) = Σ (K - |n|) R(N + n)`: since `R ≥ 0`,
`S(K) - S(K - h) ≤ h Σ_{|n| ≤ K} R(N + n) ≤ S(K + h) - S(K)`, and `S(K') ~ K'² N` at
`K' = K, K ± h` with `h = K/m` gives `Σ_{|n| ≤ K} R(N + n) = 2 K N (1 + O(1/m) + o(1))`.

* `ScW`: a weighted sum `Σ_{j ≤ 2M} w(j - M) R(N + j - M)` centred at `M`, and `ScW_shift`, it does
  not depend on `M` once the weight vanishes past `K ≤ M`;
* `fejer_diff_upper`, `fejer_diff_lower`: the two difference inequalities, unconditional;
* `rsum_asymp_rh`: **under RH**, for `K = K(N)` with `log² N = o(K)` and `4 K² ≤ N`,
  `Σ_{|n| ≤ K} R(N + n) ~ 2 K N`, PROVED CONDITIONAL ON RiemannHypothesis only.

Binary Goldbach is OPEN.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset Filter

/-- A weighted sum centred at `M`. -/
noncomputable def ScW (w : ℝ → ℝ) (N M : ℕ) : ℝ :=
  ∑ j ∈ range (2 * M + 1), w ((j : ℝ) - M) * Rg (N + j - M)

/-- The Fejér weight `max(K - |t|, 0)`. -/
noncomputable def wF (K : ℕ) (t : ℝ) : ℝ := max ((K : ℝ) - |t|) 0

/-- The indicator of `|t| ≤ K`. -/
noncomputable def wI (K : ℕ) (t : ℝ) : ℝ := if |t| ≤ K then 1 else 0

/-- `Σ_{|n| ≤ K} R(N + n)`. -/
noncomputable def Rsum (N K : ℕ) : ℝ := ∑ j ∈ range (2 * K + 1), Rg (N + j - K)

lemma ScW_shift (w : ℝ → ℝ) (N K M M' : ℕ) (hw : ∀ t : ℝ, (K : ℝ) < |t| → w t = 0)
    (hKM : K ≤ M) (hMM' : M ≤ M') : ScW w N M = ScW w N M' := by
  unfold ScW
  set d := M' - M with hd
  rw [← sum_range_add_sum_Ico _ (by omega : d ≤ 2 * M' + 1),
    ← sum_Ico_consecutive _ (by omega : d ≤ d + (2 * M + 1)) (by omega : d + (2 * M + 1) ≤ 2 * M' + 1)]
  have hz1 : ∑ j ∈ range d, w ((j : ℝ) - M') * Rg (N + j - M') = 0 := by
    apply sum_eq_zero; intro j hj
    have := mem_range.mp hj
    rw [hw, zero_mul]
    have h1 : (j : ℝ) + K < M' := by
      have : j + K < M' := by omega
      exact_mod_cast this
    rw [abs_of_neg (by linarith)]; linarith
  have hz3 : ∑ j ∈ Ico (d + (2 * M + 1)) (2 * M' + 1), w ((j : ℝ) - M') * Rg (N + j - M') = 0 := by
    apply sum_eq_zero; intro j hj
    have := mem_Ico.mp hj
    rw [hw, zero_mul]
    have h1 : (M' : ℝ) + K < j := by
      have : M' + K < j := by omega
      exact_mod_cast this
    rw [abs_of_pos (by linarith)]; linarith
  rw [hz1, hz3, zero_add, add_zero, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  apply sum_congr rfl; intro i hi
  have hi' := mem_range.mp hi
  congr 1
  · congr 1; push_cast; rw [hd, Nat.cast_sub hMM']; ring
  · congr 1; omega

lemma wF_zero {K : ℕ} {t : ℝ} (h : (K : ℝ) < |t|) : wF K t = 0 := by
  unfold wF; rw [max_eq_right (by linarith)]

lemma wI_zero {K : ℕ} {t : ℝ} (h : (K : ℝ) < |t|) : wI K t = 0 := by
  unfold wI; rw [if_neg (by linarith)]

lemma fejer_eq_ScW (N K : ℕ) : fejer N K = ScW (wF K) N K := by
  unfold fejer ScW
  apply sum_congr rfl; intro j hj
  have hj' : j ≤ 2 * K := by have := mem_range.mp hj; omega
  unfold wF; rw [max_eq_left (Thm6.weight_nonneg K j hj')]

lemma Rsum_eq_ScW (N K : ℕ) : Rsum N K = ScW (wI K) N K := by
  unfold Rsum ScW
  apply sum_congr rfl; intro j hj
  have hj' : j ≤ 2 * K := by have := mem_range.mp hj; omega
  unfold wI
  rw [if_pos, one_mul]
  rw [abs_le]
  have : (j : ℝ) ≤ 2 * K := by exact_mod_cast hj'
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  constructor <;> linarith

lemma ScW_mono (w v : ℝ → ℝ) (N M : ℕ) (h : ∀ t, w t ≤ v t) : ScW w N M ≤ ScW v N M :=
  sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h _) (Rg_nonneg _)

lemma ScW_sub (w v : ℝ → ℝ) (N M : ℕ) :
    ScW w N M - ScW v N M = ScW (fun t => w t - v t) N M := by
  unfold ScW; rw [← sum_sub_distrib]; apply sum_congr rfl; intro j _; ring

lemma ScW_smul (c : ℝ) (w : ℝ → ℝ) (N M : ℕ) :
    c * ScW w N M = ScW (fun t => c * w t) N M := by
  unfold ScW; rw [mul_sum]; apply sum_congr rfl; intro j _; ring

/-- `h Σ_{|n| ≤ K} R(N + n) ≤ S(K + h) - S(K)`. -/
lemma fejer_diff_upper (N K h : ℕ) :
    (h : ℝ) * Rsum N K ≤ fejer N (K + h) - fejer N K := by
  rw [fejer_eq_ScW, fejer_eq_ScW, Rsum_eq_ScW,
    ScW_shift (wF K) N K K (K + h) (fun t ht => wF_zero ht) le_rfl (by omega),
    ScW_shift (wI K) N K K (K + h) (fun t ht => wI_zero ht) le_rfl (by omega),
    ScW_sub, ScW_smul]
  apply ScW_mono; intro t
  unfold wI wF
  split_ifs with ht
  · push_cast
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
  · rw [mul_zero]
    push_cast
    have := le_max_right ((K : ℝ) + h - |t|) 0
    have h2 : max ((K : ℝ) - |t|) 0 ≤ max ((K : ℝ) + h - |t|) 0 :=
      max_le_max (by have : (0 : ℝ) ≤ h := Nat.cast_nonneg h; linarith) le_rfl
    linarith

/-- `S(K) - S(K - h) ≤ h Σ_{|n| ≤ K} R(N + n)`. -/
lemma fejer_diff_lower (N K h : ℕ) (hhK : h ≤ K) :
    fejer N K - fejer N (K - h) ≤ (h : ℝ) * Rsum N K := by
  rw [fejer_eq_ScW, fejer_eq_ScW, Rsum_eq_ScW,
    ScW_shift (wF (K - h)) N (K - h) (K - h) K (fun t ht => wF_zero ht) le_rfl (by omega),
    ScW_sub, ScW_smul]
  apply ScW_mono; intro t
  unfold wI wF
  have hc : ((K - h : ℕ) : ℝ) = K - h := Nat.cast_sub hhK
  rw [hc]
  split_ifs with ht
  · rw [mul_one]
    have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    rcases le_total ((K : ℝ) - h - |t|) 0 with h1 | h1
    · rw [max_eq_right h1, max_eq_left (by linarith)]
      have : (K : ℝ) - |t| ≤ h := by linarith
      linarith
    · rw [max_eq_left h1, max_eq_left (by linarith)]; linarith
  · push_neg at ht
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]; simp

/-- The algebra of the differencing step: from `S(K') = K'² N (1 + O(η))` at `K' = K, K ± h`,
with `h ≤ K/m`, `K ≤ 2 m h`, `η = δ/(10 m)` and `m ≥ 2/δ`, `|Σ R - 2 K N| < 2 δ K N`. -/
lemma diff_algebra {k hh n R F0 Fp Fm δ m : ℝ} (hk : 0 < k) (hh0 : 0 < hh) (hn : 0 < n)
    (hδ : 0 < δ) (hm2 : 2 / δ ≤ m) (hm1 : 1 ≤ m) (hhk : hh * m ≤ k) (hkh : k ≤ 2 * m * hh)
    (hU : hh * R ≤ Fp - F0) (hL : F0 - Fm ≤ hh * R)
    (hF0 : |F0 - k ^ 2 * n| ≤ δ / (10 * m) * (k ^ 2 * n))
    (hFp : |Fp - (k + hh) ^ 2 * n| ≤ δ / (10 * m) * ((k + hh) ^ 2 * n))
    (hFm : |Fm - (k - hh) ^ 2 * n| ≤ δ / (10 * m) * ((k - hh) ^ 2 * n)) :
    |R - 2 * k * n| < δ * (2 * k * n) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm2
  have hδm : 2 ≤ δ * m := by rw [div_le_iff₀ hδ] at hm2; linarith
  set η := δ / (10 * m) with hη
  have hη0 : 0 < η := by positivity
  have hηm : η * (10 * m) = δ := by rw [hη]; field_simp
  have hhk' : hh ≤ k := by nlinarith [mul_le_mul_of_nonneg_left hm1 hh0.le]
  rw [abs_le] at hF0 hFp hFm
  -- hh² ≤ δ hh k / 2
  have e1 : hh ^ 2 * 2 ≤ δ * hh * k := by
    have : hh * 2 ≤ δ * k := by nlinarith
    nlinarith
  -- η k² ≤ δ hh k / 5
  have e2 : η * k ^ 2 * 5 ≤ δ * hh * k := by
    have : η * k * 5 ≤ δ * hh := by
      have h1 : η * k ≤ η * (2 * m * hh) := mul_le_mul_of_nonneg_left hkh hη0.le
      have h2 : η * (2 * m * hh) * 5 = δ * hh := by
        have : η * (2 * m * hh) * 5 = (η * (10 * m)) * hh := by ring
        rw [this, hηm]
      linarith
    nlinarith
  rw [abs_lt]
  constructor
  · -- lower bound
    have hk2 : (k - hh) ^ 2 ≤ k ^ 2 := by nlinarith
    have : hh * (2 * k * n - R) ≤ hh ^ 2 * n + 2 * η * k ^ 2 * n := by
      have hFm' : Fm ≤ (k - hh) ^ 2 * n + η * (k ^ 2 * n) := by
        have : η * ((k - hh) ^ 2 * n) ≤ η * (k ^ 2 * n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk2 hn.le) hη0.le
        linarith [hFm.2]
      nlinarith [hF0.1]
    have h3 : hh * (2 * k * n - R) < hh * (δ * (2 * k * n)) := by
      have : hh ^ 2 * n + 2 * η * k ^ 2 * n < hh * (δ * (2 * k * n)) := by
        have := mul_le_mul_of_nonneg_right e1 hn.le
        have := mul_le_mul_of_nonneg_right e2 hn.le
        have : 0 < δ * hh * k * n := by positivity
        nlinarith
      linarith
    have := lt_of_mul_lt_mul_left h3 hh0.le
    linarith
  · -- upper bound
    have hk2 : (k + hh) ^ 2 ≤ 4 * k ^ 2 := by nlinarith
    have : hh * (R - 2 * k * n) ≤ hh ^ 2 * n + 5 * η * k ^ 2 * n := by
      have hFp' : Fp ≤ (k + hh) ^ 2 * n + 4 * η * (k ^ 2 * n) := by
        have : η * ((k + hh) ^ 2 * n) ≤ η * (4 * k ^ 2 * n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk2 hn.le) hη0.le
        linarith [hFp.2]
      nlinarith [hF0.1]
    have h3 : hh * (R - 2 * k * n) < hh * (δ * (2 * k * n)) := by
      have : hh ^ 2 * n + 5 * η * k ^ 2 * n < hh * (δ * (2 * k * n)) := by
        have := mul_le_mul_of_nonneg_right e1 hn.le
        have := mul_le_mul_of_nonneg_right e2 hn.le
        have : 0 < δ * hh * k * n := by positivity
        nlinarith
      linarith
    have := lt_of_mul_lt_mul_left h3 hh0.le
    linarith

/-- `|x/D - 1| < δ` from `|x - D| < δ D`. -/
lemma dist_div_lt {x D δ : ℝ} (hD : 0 < D) (h : |x - D| < δ * D) : dist (x / D) 1 < δ := by
  rw [Real.dist_eq, show x / D - 1 = (x - D) / D by field_simp, abs_div, abs_of_pos hD,
    div_lt_iff₀ hD]
  exact h

/-- `|F - D| ≤ η D` from `|F/D - 1| < η`. -/
lemma abs_sub_le_of_dist {x D η : ℝ} (hD : 0 < D) (h : dist (x / D) 1 < η) : |x - D| ≤ η * D := by
  rw [Real.dist_eq, show x / D - 1 = (x - D) / D by field_simp, abs_div, abs_of_pos hD,
    div_lt_iff₀ hD] at h
  exact h.le

/-- **Goldston, Section 5, under RH.** For `K = K(N)` with `log² N = o(K)` and `4 K² ≤ N`,
`Σ_{|n| ≤ K} R(N + n) ~ 2 K N`. PROVED CONDITIONAL ON RiemannHypothesis only. -/
theorem rsum_asymp_rh (hRH : RiemannHypothesis) (K : ℕ → ℕ)
    (hlog : Tendsto (fun N : ℕ => Real.log N ^ 2 / K N) atTop (nhds 0))
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ 4 * (K N * K N) ≤ N) :
    Tendsto (fun N : ℕ => Rsum N (K N) / (2 * K N * N)) atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set m : ℕ := ⌈2 / δ⌉₊ + 2 with hm
  have hm2 : 2 / δ ≤ (m : ℝ) := by
    have := Nat.le_ceil (2 / δ); rw [hm]; push_cast; linarith
  have hm1 : (2 : ℕ) ≤ m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  set η : ℝ := δ / (10 * m) with hη
  have hη0 : 0 < η := by positivity
  -- eventually log N ≥ 1 and K large
  have eL : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have eS : ∀ᶠ N : ℕ in atTop, Real.log N ^ 2 / K N < 1 / (2 * m) :=
    hlog.eventually (Iio_mem_nhds (by positivity))
  have eBig : ∀ᶠ N : ℕ in atTop, 2 * m ≤ K N := by
    filter_upwards [eL, eS, hK] with N hL hS hKN
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast hKN.1
    rw [div_lt_iff₀ hKpos] at hS
    have hl2 : 1 ≤ Real.log N ^ 2 := by nlinarith
    have : (2 * m : ℝ) < K N := by
      have h2 : 1 < 1 / (2 * m) * (K N : ℝ) := by linarith
      rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ (by positivity)] at h2
      linarith
    exact_mod_cast this.le
  have hK1 : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ K N * K N ≤ N := by
    filter_upwards [hK] with N h; exact ⟨h.1, by nlinarith [h.2]⟩
  -- the three Fejér asymptotics
  set Kp : ℕ → ℕ := fun N => K N + K N / m with hKp
  set Km : ℕ → ℕ := fun N => K N - K N / m with hKm
  have hdiv : ∀ N, K N / m ≤ K N / 2 := fun N => Nat.div_le_div_left hm1 (by norm_num)
  have tp : Tendsto (fun N : ℕ => Real.log N ^ 2 / Kp N) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
    · filter_upwards with N; positivity
    · filter_upwards [hK] with N h
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast h.1)
      simp only [hKp]; push_cast; linarith [(Nat.cast_nonneg (K N / m) : (0 : ℝ) ≤ _)]
  have tm : Tendsto (fun N : ℕ => Real.log N ^ 2 / Km N) atTop (nhds 0) := by
    have h2 : Tendsto (fun N : ℕ => 2 * (Real.log N ^ 2 / K N)) atTop (nhds 0) := by
      simpa using hlog.const_mul 2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    · filter_upwards with N; positivity
    · filter_upwards [hK, eBig] with N h hb
      have hKm2 : (K N : ℝ) / 2 ≤ Km N := by
        simp only [hKm]
        have := hdiv N
        have h3 : K N / 2 * 2 ≤ K N := Nat.div_mul_le_self _ _
        have h4 : K N - K N / m ≥ K N - K N / 2 := by omega
        have h5 : ((K N - K N / 2 : ℕ) : ℝ) * 2 ≥ K N := by
          have : (K N - K N / 2) * 2 ≥ K N := by omega
          exact_mod_cast this
        have h6 : ((K N - K N / m : ℕ) : ℝ) ≥ ((K N - K N / 2 : ℕ) : ℝ) := by exact_mod_cast h4
        linarith
      have hKpos : (0 : ℝ) < K N := by exact_mod_cast h.1
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) hKpos]
      have : 0 ≤ Real.log N ^ 2 := sq_nonneg _
      nlinarith
  have aK := fejer_asymp_rh hRH K hlog hK1
  have aP := fejer_asymp_rh hRH Kp tp (by
    filter_upwards [hK] with N h
    refine ⟨le_trans h.1 (Nat.le_add_right _ _), ?_⟩
    have : Kp N ≤ 2 * K N := by simp only [hKp]; have := hdiv N; omega
    nlinarith)
  have aM := fejer_asymp_rh hRH Km tm (by
    filter_upwards [hK, eBig] with N h hb
    refine ⟨?_, ?_⟩
    · simp only [hKm]; have := hdiv N; omega
    · have : Km N ≤ K N := Nat.sub_le _ _
      nlinarith [h.2])
  rw [Metric.tendsto_atTop] at aK aP aM
  obtain ⟨A1, hA1⟩ := aK η hη0
  obtain ⟨A2, hA2⟩ := aP η hη0
  obtain ⟨A3, hA3⟩ := aM η hη0
  obtain ⟨A4, hA4⟩ := eventually_atTop.1 (hK.and eBig)
  refine ⟨max (max A1 A2) (max A3 A4), fun N hN => ?_⟩
  have hN1 : A1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : A2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : A3 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN4 : A4 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨⟨hKN1, hKN4⟩, hb⟩ := hA4 N hN4
  set h := K N / m with hhdef
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := by nlinarith
    exact_mod_cast this
  have hkpos : (0 : ℝ) < K N := by exact_mod_cast hKN1
  have hhm : h * m ≤ K N := Nat.div_mul_le_self _ _
  have hmh : K N < (h + 1) * m := by
    have := Nat.lt_div_mul_add (a := K N) (show 0 < m by omega)
    rw [← hhdef] at this
    calc K N < h * m + m := this
      _ = (h + 1) * m := by ring
  have hh1 : 1 ≤ h := by
    rw [hhdef]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hh1
  have hhkR : (h : ℝ) * m ≤ K N := by exact_mod_cast hhm
  have hkhR : (K N : ℝ) ≤ 2 * m * h := by
    have : K N ≤ 2 * m * h := by nlinarith
    exact_mod_cast this
  have hU := fejer_diff_upper N (K N) h
  have hL := fejer_diff_lower N (K N) h (by rw [hhdef]; exact Nat.div_le_self _ _)
  have hD0 : (0 : ℝ) < (K N : ℝ) ^ 2 * N := by positivity
  have hF0 := abs_sub_le_of_dist hD0 (hA1 N hN1)
  have hFp := abs_sub_le_of_dist (show (0 : ℝ) < (Kp N : ℝ) ^ 2 * N by
    have : (0 : ℝ) < Kp N := by simp only [hKp]; push_cast; positivity
    positivity) (hA2 N hN2)
  have hFm := abs_sub_le_of_dist (show (0 : ℝ) < (Km N : ℝ) ^ 2 * N by
    have : (0 : ℝ) < Km N := by
      have : 1 ≤ Km N := by simp only [hKm]; have := hdiv N; omega
      exact_mod_cast this
    positivity) (hA3 N hN3)
  have eKp : (Kp N : ℝ) = K N + h := by simp only [hKp]; push_cast; rfl
  have eKm : (Km N : ℝ) = K N - h := by
    simp only [hKm]; rw [Nat.cast_sub (Nat.div_le_self _ _)]
  rw [eKp] at hFp
  rw [eKm] at hFm
  have hfp : fejer N (Kp N) = fejer N (K N + h) := rfl
  have hfm : fejer N (Km N) = fejer N (K N - h) := rfl
  rw [hfp] at hFp
  rw [hfm] at hFm
  apply dist_div_lt (by positivity)
  exact diff_algebra hkpos hhpos hNpos hδ hm2 (by exact_mod_cast (show 1 ≤ m by omega)) hhkR hkhR
    hU hL hF0 hFp hFm

end LeanLab.GoldbachGaps.Goldston1990
