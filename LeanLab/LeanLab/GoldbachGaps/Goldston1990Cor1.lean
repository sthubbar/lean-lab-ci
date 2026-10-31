import LeanLab.GoldbachGaps.Goldston1990Sec5

/-!
# Goldston 1990, Corollary 1 under RH, centred form, no cited input

Lab proof, unit U-6303, CLOUD 20261020T1017Z-cloud40, P0030. AI wrote this file. Known
mathematics, Goldston 1990, Section 5, page 292.

`rsumr_asymp_rh`: under RH, for `K = K(N)` with `log² N = o(K)` and `4 K² ≤ N`,
`Σ_{|n| ≤ K} r(N + n) ~ 2 K N / log² N`, where `r(n)` counts ordered pairs of primes with sum
`n`. This is Corollary 1 on the interval `[N - K, N + K]`; the paper states it on `[N, N + K]`
"after a relabeling of the variables", which this file does not do in Lean. PROVED CONDITIONAL
ON RiemannHypothesis only, from `rsum_asymp_rh` and

* `Rg_le_rg`: `R(n) ≤ r(n) log² M` for `n ≤ M`;
* `rg_le_Rg`: `r(n) ≤ R(n)/log² y + 2(y + 1)` for `y > 1`, pairs with both primes at least `y`
  and the rest; used with `y = N/log⁴ N`.

Binary Goldbach is OPEN.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset Filter

/-- `Σ_{|n| ≤ K} r(N + n)`. -/
noncomputable def rsumr (N K : ℕ) : ℝ := ∑ j ∈ range (2 * K + 1), (rg (N + j - K) : ℝ)

lemma rg_eq_sum (n : ℕ) :
    (rg n : ℝ) = ∑ p ∈ range n, if p.Prime ∧ (n - p).Prime then (1 : ℝ) else 0 := by
  unfold rg; rw [← sum_boole]

lemma Rg_le_rg {n M : ℕ} (hn : n ≤ M) : Rg n ≤ rg n * Real.log M ^ 2 := by
  rw [rg_eq_sum, sum_mul]
  unfold Rg
  apply sum_le_sum; intro p hp
  have hp' := mem_range.mp hp
  split_ifs with h
  · rw [one_mul, sq]
    have h1 : Real.log p ≤ Real.log M :=
      Real.log_le_log (by exact_mod_cast h.1.pos) (by exact_mod_cast (by omega : p ≤ M))
    have h2 : Real.log ((n - p : ℕ) : ℝ) ≤ Real.log M :=
      Real.log_le_log (by exact_mod_cast h.2.pos) (by exact_mod_cast (by omega : n - p ≤ M))
    have h3 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have h4 : 0 ≤ Real.log ((n - p : ℕ) : ℝ) := Real.log_natCast_nonneg _
    exact mul_le_mul h1 h2 h4 (le_trans h3 h1)
  · simp

lemma card_small_le (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (((range n).filter (fun p : ℕ => (p : ℝ) < y ∨ ((n - p : ℕ) : ℝ) < y)).card : ℝ) ≤ 2 * (y + 1) := by
  have hsub : (range n).filter (fun p : ℕ => (p : ℝ) < y ∨ ((n - p : ℕ) : ℝ) < y) ⊆
      range ⌈y⌉₊ ∪ (range ⌈y⌉₊).image (fun q : ℕ => n - q) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    simp only [mem_union, mem_range, mem_image]
    rcases hp.2 with h | h
    · left; exact Nat.lt_ceil.mpr h
    · right; exact ⟨n - p, Nat.lt_ceil.mpr h, by omega⟩
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hi := card_image_le (s := range ⌈y⌉₊) (f := fun q => n - q)
  rw [card_range] at hc hi
  have : ((range n).filter (fun p : ℕ => (p : ℝ) < y ∨ ((n - p : ℕ) : ℝ) < y)).card ≤ 2 * ⌈y⌉₊ := by
    omega
  have hce : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy
  have : (((range n).filter (fun p : ℕ => (p : ℝ) < y ∨ ((n - p : ℕ) : ℝ) < y)).card : ℝ) ≤
      2 * (⌈y⌉₊ : ℝ) := by exact_mod_cast this
  linarith

lemma rg_le_Rg (n : ℕ) {y : ℝ} (hy : 1 < y) :
    (rg n : ℝ) ≤ Rg n / Real.log y ^ 2 + 2 * (y + 1) := by
  have hL : 0 < Real.log y := Real.log_pos hy
  have hL2 : 0 < Real.log y ^ 2 := by positivity
  have hpt : ∀ p ∈ range n, (if p.Prime ∧ (n - p).Prime then (1 : ℝ) else 0) ≤
      (if p.Prime ∧ (n - p).Prime then Real.log p * Real.log ((n - p : ℕ) : ℝ) else 0) /
        Real.log y ^ 2 + (if (p : ℝ) < y ∨ ((n - p : ℕ) : ℝ) < y then 1 else 0) := by
    intro p _
    by_cases hP : p.Prime ∧ (n - p).Prime
    · rw [if_pos hP, if_pos hP]
      by_cases hs : (p : ℝ) < y ∨ ((n - p : ℕ) : ℝ) < y
      · rw [if_pos hs]
        have : 0 ≤ Real.log p * Real.log ((n - p : ℕ) : ℝ) / Real.log y ^ 2 := by
          apply div_nonneg _ hL2.le
          exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
        linarith
      · rw [if_neg hs, add_zero, le_div_iff₀ hL2, one_mul, sq]
        push_neg at hs
        have h1 := Real.log_le_log (by linarith) hs.1
        have h2 := Real.log_le_log (by linarith) hs.2
        exact mul_le_mul h1 h2 hL.le (le_trans hL.le h1)
    · rw [if_neg hP, if_neg hP, zero_div, zero_add]
      split_ifs <;> norm_num
  rw [rg_eq_sum]
  calc ∑ p ∈ range n, (if p.Prime ∧ (n - p).Prime then (1 : ℝ) else 0)
      ≤ ∑ p ∈ range n, ((if p.Prime ∧ (n - p).Prime then
          Real.log p * Real.log ((n - p : ℕ) : ℝ) else 0) / Real.log y ^ 2 +
          (if (p : ℝ) < y ∨ ((n - p : ℕ) : ℝ) < y then 1 else 0)) := sum_le_sum hpt
    _ = Rg n / Real.log y ^ 2 +
          (((range n).filter (fun p : ℕ => (p : ℝ) < y ∨ ((n - p : ℕ) : ℝ) < y)).card : ℝ) := by
        rw [sum_add_distrib, ← sum_div, sum_boole]; rfl
    _ ≤ Rg n / Real.log y ^ 2 + 2 * (y + 1) := by
        have := card_small_le n (show 0 ≤ y by linarith); linarith

lemma rsumr_ge (N K : ℕ) : Rsum N K / Real.log (N + K) ^ 2 ≤ rsumr N K := by
  rcases eq_or_lt_of_le (sq_nonneg (Real.log (N + K))) with h0 | hpos
  · rw [← h0, div_zero]; exact sum_nonneg fun _ _ => Nat.cast_nonneg _
  rw [div_le_iff₀ hpos]
  unfold Rsum rsumr
  rw [sum_mul]
  apply sum_le_sum; intro j hj
  have hj' := mem_range.mp hj
  have := Rg_le_rg (n := N + j - K) (M := N + K) (by omega)
  push_cast at this
  exact this

lemma rsumr_le (N K : ℕ) {y : ℝ} (hy : 1 < y) :
    rsumr N K ≤ Rsum N K / Real.log y ^ 2 + (2 * K + 1) * (2 * (y + 1)) := by
  unfold Rsum rsumr
  calc ∑ j ∈ range (2 * K + 1), (rg (N + j - K) : ℝ)
      ≤ ∑ j ∈ range (2 * K + 1), (Rg (N + j - K) / Real.log y ^ 2 + 2 * (y + 1)) :=
        sum_le_sum fun j _ => rg_le_Rg _ hy
    _ = _ := by rw [sum_add_distrib, ← sum_div, sum_const, card_range, nsmul_eq_mul]; push_cast; ring

lemma cor1_lower {R r L Lk D δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL1 : 1 ≤ L) (hL24 : 24 ≤ δ * L)
    (hD : 0 < D) (hRlo : (1 - δ / 4) * D ≤ R) (hge : R / Lk ^ 2 ≤ r) (hLk0 : 0 < Lk)
    (hLk : Lk ≤ L + 1) : 1 - δ < r * L ^ 2 / D := by
  have hR0 : 0 ≤ R := le_trans (by nlinarith) hRlo
  have h1 : R / (L + 1) ^ 2 ≤ r :=
    le_trans (div_le_div_of_nonneg_left hR0 (by positivity) (pow_le_pow_left₀ hLk0.le hLk 2)) hge
  rw [div_le_iff₀ (by positivity)] at h1
  have hratio : (1 - δ / 4) * (L + 1) ^ 2 ≤ L ^ 2 := by nlinarith
  rw [lt_div_iff₀ hD]
  have hA : 0 ≤ 1 - δ / 4 := by linarith
  -- r L² ≥ R L²/(L+1)² ≥ (1-δ/4) D (1-δ/4)
  have h2 : (1 - δ / 4) * D * ((1 - δ / 4) * (L + 1) ^ 2) ≤ R * L ^ 2 :=
    mul_le_mul hRlo hratio (by nlinarith) hR0
  have h3 : R * L ^ 2 ≤ r * (L + 1) ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg L)
  have hL2 : 0 < (L + 1) ^ 2 := by positivity
  have h4 : (1 - δ / 4) * D * (1 - δ / 4) ≤ r * L ^ 2 := by
    have : ((1 - δ / 4) * D * (1 - δ / 4)) * (L + 1) ^ 2 ≤ (r * L ^ 2) * (L + 1) ^ 2 := by
      nlinarith
    exact le_of_mul_le_mul_right this hL2
  nlinarith

lemma cor1_upper {R r L Ly D δ ε E : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε5 : ε ≤ 1 / 5)
    (hεδ : ε ≤ δ / 10) (hL : 0 < L) (hLy : (1 - ε) * L ≤ Ly) (hD : 0 < D)
    (hRhi : R ≤ (1 + δ / 4) * D) (hR0 : 0 ≤ R) (hle : r ≤ R / Ly ^ 2 + E)
    (hE : E * L ^ 2 ≤ δ / 4 * D) : r * L ^ 2 / D < 1 + δ := by
  have hpos : 0 < (1 - ε) * L := by nlinarith
  have h1 : R / Ly ^ 2 ≤ R / ((1 - ε) * L) ^ 2 :=
    div_le_div_of_nonneg_left hR0 (by positivity) (pow_le_pow_left₀ hpos.le hLy 2)
  have hinv : 1 ≤ (1 + 3 * ε) * (1 - ε) ^ 2 := by
    have e : (1 + 3 * ε) * (1 - ε) ^ 2 - 1 = ε * (1 - 5 * ε + 3 * ε ^ 2) := by ring
    have : 0 ≤ ε * (1 - 5 * ε + 3 * ε ^ 2) := mul_nonneg hε.le (by nlinarith)
    linarith
  have h2 : R / ((1 - ε) * L) ^ 2 * L ^ 2 ≤ (1 + δ / 4) * (1 + 3 * ε) * D := by
    rw [mul_pow, div_mul_eq_mul_div, div_le_iff₀ (by have := pow_pos hpos 2; rwa [mul_pow] at this)]
    have hq : 0 ≤ (1 + δ / 4) * D * L ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hinv hq, mul_le_mul_of_nonneg_right hRhi (sq_nonneg L)]
  have h3 : r * L ^ 2 ≤ (1 + δ / 4) * (1 + 3 * ε) * D + δ / 4 * D := by
    have := mul_le_mul_of_nonneg_right (hle.trans (by linarith [h1] :
      R / Ly ^ 2 + E ≤ R / ((1 - ε) * L) ^ 2 + E)) (sq_nonneg L)
    rw [add_mul] at this; linarith
  rw [div_lt_iff₀ hD]
  have : (1 + δ / 4) * (1 + 3 * ε) + δ / 4 < 1 + δ := by nlinarith
  nlinarith

lemma cor1_E {k n L δ y : ℝ} (hk : 1 ≤ k) (hn : 0 < n) (hL : 1 ≤ L) (hL24 : 24 ≤ δ * L)
    (hδ : 0 < δ) (hy : y * L ^ 4 = n) (h4 : L ^ 4 ≤ δ / 24 * n) :
    (2 * k + 1) * (2 * (y + 1)) * L ^ 2 ≤ δ / 4 * (2 * k * n) := by
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hL24b : 24 ≤ δ * L ^ 2 := le_trans hL24 (mul_le_mul_of_nonneg_left hL2 hδ.le)
  have hL4 : L ^ 2 ≤ L ^ 4 := by nlinarith
  have e1 : y * L ^ 2 * 24 ≤ δ * n := by
    have : y * L ^ 2 * 24 ≤ y * L ^ 2 * (δ * L ^ 2) :=
      mul_le_mul_of_nonneg_left hL24b (by
        have : 0 ≤ y * L ^ 4 := by rw [hy]; exact hn.le
        nlinarith [pow_pos (show (0:ℝ) < L by linarith) 4])
    have e : y * L ^ 2 * (δ * L ^ 2) = δ * (y * L ^ 4) := by ring
    rw [e, hy] at this; exact this
  have e3 : L ^ 2 * 24 ≤ δ * n := by nlinarith
  have hyL : 2 * (y + 1) * L ^ 2 ≤ δ / 6 * n := by nlinarith
  have hk1 : 2 * k + 1 ≤ 3 / 2 * (2 * k) := by linarith
  have h0 : 0 ≤ 2 * (y + 1) * L ^ 2 := by
    have : 0 ≤ y * L ^ 2 := by
      have : 0 ≤ y * L ^ 4 := by rw [hy]; exact hn.le
      nlinarith [pow_pos (show (0:ℝ) < L by linarith) 2]
    nlinarith
  calc (2 * k + 1) * (2 * (y + 1)) * L ^ 2 = (2 * k + 1) * (2 * (y + 1) * L ^ 2) := by ring
    _ ≤ (3 / 2 * (2 * k)) * (δ / 6 * n) := mul_le_mul hk1 hyL h0 (by linarith)
    _ = δ / 4 * (2 * k * n) := by ring

/-- **Goldston's Corollary 1 under RH, centred form.** For `K = K(N)` with `log² N = o(K)` and
`4 K² ≤ N`, `Σ_{|n| ≤ K} r(N + n) ~ 2 K N / log² N`. PROVED CONDITIONAL ON RiemannHypothesis
only. -/
theorem rsumr_asymp_rh (hRH : RiemannHypothesis) (K : ℕ → ℕ)
    (hlog : Tendsto (fun N : ℕ => Real.log N ^ 2 / K N) atTop (nhds 0))
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ 4 * (K N * K N) ≤ N) :
    Tendsto (fun N : ℕ => rsumr N (K N) / (2 * K N * N / Real.log N ^ 2)) atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro δ0 hδ0
  set δ := min δ0 1 with hδdef
  have hδ : 0 < δ := lt_min hδ0 one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set ε := min (1 / 5 : ℝ) (δ / 10) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε5 : ε ≤ 1 / 5 := min_le_left _ _
  have hεδ : ε ≤ δ / 10 := min_le_right _ _
  have aR := rsum_asymp_rh hRH K hlog hK
  rw [Metric.tendsto_atTop] at aR
  obtain ⟨A1, hA1⟩ := aR (δ / 4) (by positivity)
  have tL := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have eL : ∀ᶠ N : ℕ in atTop, max (max 1 (64 / ε ^ 2)) (max (8 / δ) (24 / δ)) ≤ Real.log N :=
    tL.eventually_ge_atTop _
  have t4 : Tendsto (fun N : ℕ => Real.log N ^ 4 / (1 * (N : ℝ) + 0)) atTop (nhds 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have e4 : ∀ᶠ N : ℕ in atTop, Real.log N ^ 4 / (1 * (N : ℝ) + 0) < δ / 24 :=
    t4.eventually (Iio_mem_nhds (by positivity))
  have eN : ∀ᶠ N : ℕ in atTop, A1 ≤ N := eventually_ge_atTop A1
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eL.and (e4.and (eN.and hK)))
  refine ⟨M, fun N hNM => ?_⟩
  obtain ⟨hLb, h4, hNA, hK1, hK4⟩ := hM N hNM
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLb
  have hL64 : 64 / ε ^ 2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLb
  have hL8 : 8 / δ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLb
  have hL24 : 24 / δ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLb
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := by nlinarith
    exact_mod_cast this
  have hkpos : (0 : ℝ) < K N := by exact_mod_cast hK1
  have hKN : (K N : ℝ) ≤ N := by
    have : K N ≤ N := by nlinarith
    exact_mod_cast this
  have hL0 : 0 < L := by linarith
  -- the R sum
  have hR := hA1 N hNA
  have hD : (0 : ℝ) < 2 * K N * N := by positivity
  rw [Real.dist_eq, abs_lt] at hR
  have hRlo : (1 - δ / 4) * (2 * K N * N) ≤ Rsum N (K N) := by
    have := hR.1; rw [lt_sub_iff_add_lt, lt_div_iff₀ hD] at this; nlinarith
  have hRhi : Rsum N (K N) ≤ (1 + δ / 4) * (2 * K N * N) := by
    have := hR.2; rw [sub_lt_iff_lt_add, div_lt_iff₀ hD] at this; nlinarith
  have hδδ : δ ≤ δ0 := min_le_left _ _
  have hL24' : 24 ≤ δ * L := by rw [div_le_iff₀ hδ] at hL24; linarith
  have hR0 : 0 ≤ Rsum N (K N) := le_trans (by nlinarith) hRlo
  rw [show rsumr N (K N) / (2 * K N * N / L ^ 2) = rsumr N (K N) * L ^ 2 / (2 * K N * N) by
    field_simp]
  rw [Real.dist_eq, abs_lt]
  constructor
  · -- lower bound
    have hlog2 : Real.log ((N : ℝ) + K N) ≤ L + 1 := by
      have h2N : (N : ℝ) + K N ≤ 2 * N := by linarith
      have := Real.log_le_log (by positivity) h2N
      rw [Real.log_mul (by norm_num) hNpos.ne'] at this
      have : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    have hlog0 : 0 < Real.log ((N : ℝ) + K N) := by
      have hN1 : (1 : ℝ) < N := by
        by_contra h; push_neg at h
        have : L ≤ 0 := by rw [hLdef]; exact Real.log_nonpos hNpos.le h
        linarith
      exact Real.log_pos (by linarith)
    have hge := rsumr_ge N (K N)
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
    have hle := rsumr_le N (K N) hy1
    have hE : (2 * K N + 1) * (2 * (y + 1)) * L ^ 2 ≤ δ / 4 * (2 * K N * N) :=
      cor1_E (by exact_mod_cast hK1) hNpos hL1 hL24' hδ
        (by rw [hydef]; field_simp) (by linarith)
    have := cor1_upper hδ hδ1 hε hε5 hεδ hL0 hlogy hD hRhi hR0 hle hE
    linarith

end LeanLab.GoldbachGaps.Goldston1990
