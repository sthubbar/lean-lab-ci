import LeanLab.GoldbachGaps.Goldston1990Main
import LeanLab.PNTPort.Selberg.AdditiveBlocks

/-!
# Goldston's variance `J(N, h)` under RH, from the lab's Selberg mean square

Lab proof, unit U-6010, CLOUD 20261020T0415Z-cloud34, T2, P0030 and IDEAS I-5100. AI wrote
this file. Known mathematics, Selberg 1943; CONDITIONAL ON RiemannHypothesis only, through
`PNTPort.Selberg.selberg_sum`.

Goldston's display 2 is `J(N, h) = ∫_1^N (θ(x + h) - θ(x) - h)² dx`, `Jg` in
`Goldston1990Main.lean`; his Corollaries 1 and 2 take `J(N, K) = o(K² N)` as their hypothesis.

* `jg_eq_sum`: for naturals `N ≥ 1`, `h`, `J(N, h) = Σ_{1 ≤ m < N} (θ(m + h) - θ(m) - h)²`, since
  `θ` is constant on `[m, m + 1)`;
* `sum_psi_sub_theta_sq`: `Σ_{1 ≤ m < N} (Δ_h(ψ - θ)(m))² ≤ 4h(N + h) log²(N + h)`, from
  `ψ - θ` increasing and at most `2√x log x`, Mathlib's `psi_sub_theta_le`;
* `jg_rh`: **under RH**, for naturals `h ≥ 1` with `h² ≤ N`,
  `J(N, h) ≤ C (h N (log(N/h) + 3)² + N^{5/4} h^{-5/8})`.
  Selberg's bound `J ≪ h N log² N` holds for every `h ≥ 1`; the lab's version reaches it for
  `h ≥ N^{2/13}`, the limit set by the remainder term of `selberg_sharp`.
* Reading: `J(N, K)/(K² N) ≪ log²(N/K)/K + N^{1/4} K^{-21/8}`, so `J(N, K) = o(K² N)`, the
  hypothesis of Goldston's Corollaries 1 and 2, whenever `N^c ≤ K ≤ √N` with `c > 2/21`;
  `jg_little_o` proves this, and `corollary1_rh` feeds it to the cited Corollary 1.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset Filter MeasureTheory

/-- `ψ - θ` is increasing. -/
lemma psi_sub_theta_mono : Monotone (fun x : ℝ => ψ x - θ x) := by
  intro x y hxy
  simp only
  rw [psi_sub_theta_eq_sum_not_prime, psi_sub_theta_eq_sum_not_prime]
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [mem_filter, mem_Ioc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_le_floor hxy)⟩, hn.2⟩
  · intro n _ _; exact ArithmeticFunction.vonMangoldt_nonneg

/-- `θ` is constant on `[m, m + 1)`, so the window error is. -/
lemma theta_window_const {m h : ℕ} {x : ℝ} (hx : x ∈ Set.Ico (m : ℝ) (m + 1)) :
    θ (x + h) - θ x - h = θ ((m : ℝ) + h) - θ m - h := by
  obtain ⟨h1, h2⟩ := hx
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg m) h1
  have f1 : ⌊x⌋₊ = m := (Nat.floor_eq_iff hx0).mpr ⟨h1, h2⟩
  have f2 : ⌊x + h⌋₊ = m + h := by
    rw [Nat.floor_eq_iff (by positivity)]; push_cast; constructor <;> linarith
  rw [theta_eq_theta_coe_floor x, theta_eq_theta_coe_floor (x + h), f1, f2]
  push_cast; ring

/-- **`J(N, h)` as a sum.** -/
theorem jg_eq_sum {N h : ℕ} (hN : 1 ≤ N) :
    Jg N h = ∑ m ∈ Ico 1 N, (θ ((m : ℝ) + h) - θ m - h) ^ 2 := by
  set f := fun x : ℝ => (θ (x + h) - θ x - h) ^ 2 with hf
  have hpiece : ∀ m : ℕ, ∫ x in (m : ℝ)..(m + 1), f x = (θ ((m : ℝ) + h) - θ m - h) ^ 2 := by
    intro m
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (θ ((m : ℝ) + h) - θ m - h) ^ 2)
        (fun x hx => by simp only [hf]; rw [theta_window_const ⟨hx.1.le, hx.2⟩]),
      setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul]
    ring
  have hii : ∀ m, 1 ≤ m → m < N → IntervalIntegrable f volume (m : ℝ) (m + 1) := by
    intro m _ _
    have hc : IntegrableOn (fun _ : ℝ => (θ ((m : ℝ) + h) - θ m - h) ^ 2) (Set.Ioo (m : ℝ) (m + 1)) :=
      integrableOn_const (by simp)
    have hIoo : IntegrableOn f (Set.Ioo (m : ℝ) (m + 1)) :=
      hc.congr_fun (fun x hx => by
        simp only [hf]; rw [theta_window_const ⟨hx.1.le, hx.2⟩]) measurableSet_Ioo
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo (μ := volume)).mpr hIoo
  have h := LeanLab.PNTPort.Selberg.sum_unit_intervals f hN hii
  unfold Jg
  push_cast at h ⊢
  rw [← h]
  exact sum_congr rfl fun m _ => hpiece m

/-- A shifted telescoping sum. -/
lemma sum_shift_sub (f : ℕ → ℝ) (N h : ℕ) :
    ∑ m ∈ range N, (f (m + h) - f m) = ∑ j ∈ range h, (f (N + j) - f j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    have : ∑ j ∈ range h, (f (N + 1 + j) - f j) =
        ∑ j ∈ range h, (f (N + j) - f j) + ∑ j ∈ range h, (f (N + (j + 1)) - f (N + j)) := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring_nf
    rw [this, sum_range_sub (fun j => f (N + j))]
    simp only [add_zero]

/-- **The prime power part.** -/
theorem sum_psi_sub_theta_sq (N h : ℕ) :
    ∑ m ∈ Ico 1 N, ((ψ ((m : ℝ) + h) - θ ((m : ℝ) + h)) - (ψ m - θ m)) ^ 2 ≤
      4 * h * (N + h) * Real.log (N + h) ^ 2 := by
  set f : ℕ → ℝ := fun n => ψ n - θ n with hf
  have hmono : Monotone f := fun a b hab => psi_sub_theta_mono (by exact_mod_cast hab)
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hf]; linarith [theta_le_psi (n : ℝ)]
  set B := 2 * Real.sqrt (N + h) * Real.log (N + h) with hB
  have hfle : ∀ n : ℕ, n ≤ N + h → f n ≤ B := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp only [hf, Nat.cast_zero, psi_zero, theta_zero, sub_zero]
      have : 0 ≤ Real.log ((N : ℝ) + h) := by
        have := Real.log_natCast_nonneg (N + h); push_cast at this; exact this
      positivity
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      have hnN : (n : ℝ) ≤ N + h := by exact_mod_cast hn
      have := psi_sub_theta_le h1
      have h2 : Real.sqrt n ≤ Real.sqrt (N + h) := Real.sqrt_le_sqrt hnN
      have h3 : Real.log n ≤ Real.log (N + h) := Real.log_le_log (by linarith) hnN
      have h4 : 0 ≤ Real.log n := Real.log_nonneg h1
      simp only [hf, hB]
      calc ψ (n : ℝ) - θ n ≤ 2 * √(n : ℝ) * Real.log n := this
        _ ≤ 2 * Real.sqrt (N + h) * Real.log (N + h) := by gcongr
  have hd0 : ∀ m, 0 ≤ f (m + h) - f m := fun m => sub_nonneg.mpr (hmono (by omega))
  have hdle : ∀ m, m < N → f (m + h) - f m ≤ B := fun m hm =>
    (sub_le_self _ (hf0 m)).trans (hfle _ (by omega))
  have hsum : ∑ m ∈ range N, (f (m + h) - f m) ≤ h * B := by
    rw [sum_shift_sub]
    calc ∑ j ∈ range h, (f (N + j) - f j) ≤ ∑ j ∈ range h, B :=
          sum_le_sum fun j hj => (sub_le_self _ (hf0 j)).trans (hfle _ (by
            have := mem_range.mp hj; omega))
      _ = h * B := by rw [sum_const, card_range, nsmul_eq_mul]
  have hcast : ∀ m : ℕ, ((ψ ((m : ℝ) + h) - θ ((m : ℝ) + h)) - (ψ m - θ m)) = f (m + h) - f m := by
    intro m; simp only [hf]; push_cast; ring
  have hB0 : 0 ≤ B := le_trans (hf0 0) (hfle 0 (by omega))
  calc ∑ m ∈ Ico 1 N, ((ψ ((m : ℝ) + h) - θ ((m : ℝ) + h)) - (ψ m - θ m)) ^ 2
      = ∑ m ∈ Ico 1 N, (f (m + h) - f m) ^ 2 := sum_congr rfl fun m _ => by rw [hcast]
    _ ≤ ∑ m ∈ range N, (f (m + h) - f m) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (fun m hm => by
          simp only [mem_Ico, mem_range] at hm ⊢; omega) (fun m _ _ => sq_nonneg _)
    _ ≤ ∑ m ∈ range N, B * (f (m + h) - f m) := by
        refine sum_le_sum fun m hm => ?_
        rw [sq]; exact mul_le_mul_of_nonneg_right (hdle m (mem_range.mp hm)) (hd0 m)
    _ = B * ∑ m ∈ range N, (f (m + h) - f m) := by rw [mul_sum]
    _ ≤ B * (h * B) := mul_le_mul_of_nonneg_left hsum hB0
    _ = 4 * h * (N + h) * Real.log (N + h) ^ 2 := by
        rw [hB]
        have hs : Real.sqrt ((N : ℝ) + h) ^ 2 = N + h := Real.sq_sqrt (by positivity)
        have e : 2 * Real.sqrt ((N : ℝ) + h) * Real.log (N + h) *
            (h * (2 * Real.sqrt ((N : ℝ) + h) * Real.log (N + h))) =
            4 * h * Real.sqrt ((N : ℝ) + h) ^ 2 * Real.log (N + h) ^ 2 := by ring
        rw [e, hs]

set_option maxHeartbeats 1000000 in
/-- **Goldston's variance under RH, from Selberg's mean square.** -/
theorem jg_rh (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N h : ℕ, 1 ≤ h → h * h ≤ N →
    Jg N h ≤ C * (h * N * (Real.log (N / h) + 3) ^ 2 + (N : ℝ) ^ (5 / 4 : ℝ) * (h : ℝ) ^ (-(5 / 8) : ℝ)) := by
  obtain ⟨C1, hC1, hs⟩ := LeanLab.PNTPort.Selberg.selberg_sum hRH
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
  set P := (N : ℝ) ^ (5 / 4 : ℝ) * (h : ℝ) ^ (-(5 / 8) : ℝ) with hP
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

/-- `(log x + 3)² x^{-c} → 0`. -/
lemma tendsto_log_sq_mul_rpow {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => (Real.log x + 3) ^ 2 * x ^ (-c)) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (c / 2)) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by positivity)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => x ^ (-(c / 2))) atTop (nhds 0) := tendsto_rpow_neg_atTop (by positivity)
  have h3 : Tendsto (fun x : ℝ => (Real.log x / x ^ (c / 2) + 3 * x ^ (-(c / 2))) ^ 2) atTop (nhds 0) := by
    have := (h1.add (h2.const_mul 3)).pow 2
    simpa using this
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have e1 : x ^ (-(c / 2)) = 1 / x ^ (c / 2) := by rw [Real.rpow_neg hx.le, one_div]
  have e2 : x ^ (-c) = 1 / (x ^ (c / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, Real.rpow_neg hx.le, one_div]; norm_num
  have hp : 0 < x ^ (c / 2) := Real.rpow_pos_of_pos hx _
  rw [e1, e2]; field_simp

set_option maxHeartbeats 1000000 in
/-- **`J(N, K) = o(K² N)` under RH**, for `N^c ≤ K ≤ √N`, `c > 2/21`: the hypothesis of
Goldston's Corollaries 1 and 2. -/
theorem jg_little_o (hRH : RiemannHypothesis) {c : ℝ} (hc : 2 / 21 < c) (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ K N ∧ K N * K N ≤ N) :
    Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) := by
  obtain ⟨C, hC, hj⟩ := jg_rh hRH
  have hc0 : 0 < c := by linarith
  set e := 21 * c / 8 - 1 / 4 with he
  have he0 : 0 < e := by rw [he]; linarith
  have hg : Tendsto (fun N : ℕ => C * ((Real.log N + 3) ^ 2 * (N : ℝ) ^ (-c) + (N : ℝ) ^ (-e)))
      atTop (nhds 0) := by
    have := ((tendsto_log_sq_mul_rpow hc0).add (tendsto_rpow_neg_atTop he0)).comp
      tendsto_natCast_atTop_atTop
    simpa using this.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards [hK, eventually_ge_atTop 1] with N hN hN1
    obtain ⟨hcK, hKN⟩ := hN
    have hK1 : 1 ≤ K N := by
      have : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow (by exact_mod_cast hN1) hc0.le
      have h2 : (1 : ℝ) ≤ K N := this.trans hcK
      exact_mod_cast h2
    have hJ0 : 0 ≤ Jg N (K N) := by
      rw [jg_eq_sum hN1]; exact sum_nonneg fun m _ => sq_nonneg _
    exact div_nonneg hJ0 (by positivity)
  · filter_upwards [hK, eventually_ge_atTop 1] with N hN hN1
    obtain ⟨hcK, hKN⟩ := hN
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < N := by linarith
    have hNc : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1r hc0.le
    have hK1 : (1 : ℝ) ≤ K N := hNc.trans hcK
    have hK0 : (0 : ℝ) < K N := by linarith
    have hKNr : (K N : ℝ) ≤ N := by
      have : (K N : ℝ) * K N ≤ N := by exact_mod_cast hKN
      nlinarith
    have hb := hj N (K N) (by exact_mod_cast hK1) hKN
    set ℓ := Real.log (N / K N) + 3 with hℓ
    have hl0 : 0 ≤ Real.log (N / K N) := Real.log_nonneg (by rw [le_div_iff₀ hK0]; linarith)
    have hl1 : Real.log (N / K N) ≤ Real.log N :=
      Real.log_le_log (by positivity) (div_le_self hN0.le hK1)
    have hden : 0 < (K N : ℝ) ^ 2 * N := by positivity
    rw [div_le_iff₀ hden]
    -- the two terms
    have t1 : (K N : ℝ) * N * ℓ ^ 2 ≤ (Real.log N + 3) ^ 2 * (N : ℝ) ^ (-c) * ((K N : ℝ) ^ 2 * N) := by
      have hNcK : (N : ℝ) ^ (-c) * K N ≥ 1 := by
        rw [Real.rpow_neg hN0.le]
        rw [ge_iff_le, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]; linarith
      have hsq : ℓ ^ 2 ≤ (Real.log N + 3) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      calc (K N : ℝ) * N * ℓ ^ 2 ≤ (K N : ℝ) * N * (Real.log N + 3) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ ≤ (K N : ℝ) * N * (Real.log N + 3) ^ 2 * ((N : ℝ) ^ (-c) * K N) :=
            le_mul_of_one_le_right (by positivity) hNcK
        _ = _ := by ring
    have t2 : (N : ℝ) ^ (5 / 4 : ℝ) * (K N : ℝ) ^ (-(5 / 8) : ℝ) ≤
        (N : ℝ) ^ (-e) * ((K N : ℝ) ^ 2 * N) := by
      -- `K^{-21/8} ≤ N^{-21c/8}`
      have hKr : (K N : ℝ) ^ (-(21 / 8) : ℝ) ≤ ((N : ℝ) ^ c) ^ (-(21 / 8) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hcK (by norm_num)
      have e1 : (K N : ℝ) ^ (-(5 / 8) : ℝ) = (K N : ℝ) ^ (-(21 / 8) : ℝ) * (K N : ℝ) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hK0]; norm_num
      have e2 : ((N : ℝ) ^ c) ^ (-(21 / 8) : ℝ) * (N : ℝ) ^ (5 / 4 : ℝ) = (N : ℝ) ^ (-e) * N := by
        rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
        have h3 : (N : ℝ) ^ (-e) * N = (N : ℝ) ^ (-e + 1) := by rw [Real.rpow_add hN0, Real.rpow_one]
        rw [h3]; congr 1; rw [he]; ring
      rw [e1]
      calc (N : ℝ) ^ (5 / 4 : ℝ) * ((K N : ℝ) ^ (-(21 / 8) : ℝ) * (K N : ℝ) ^ 2)
          ≤ (N : ℝ) ^ (5 / 4 : ℝ) * (((N : ℝ) ^ c) ^ (-(21 / 8) : ℝ) * (K N : ℝ) ^ 2) := by
            gcongr
        _ = (((N : ℝ) ^ c) ^ (-(21 / 8) : ℝ) * (N : ℝ) ^ (5 / 4 : ℝ)) * (K N : ℝ) ^ 2 := by ring
        _ = _ := by rw [e2]; ring
    have := mul_le_mul_of_nonneg_left (add_le_add t1 t2) hC
    calc Jg N (K N) ≤ C * ((K N : ℝ) * N * ℓ ^ 2 + (N : ℝ) ^ (5 / 4 : ℝ) * (K N : ℝ) ^ (-(5 / 8) : ℝ)) := hb
      _ ≤ _ := this
      _ = _ := by ring

/-- `√N ≤ N / log³ N` for large `N`. -/
lemma eventually_sqrt_le : ∀ᶠ N : ℕ in atTop, Real.sqrt N ≤ N / Real.log N ^ 3 := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).bound (by norm_num : (0 : ℝ) < 1)
  have h' := tendsto_natCast_atTop_atTop.eventually (h.and (eventually_gt_atTop (1 : ℝ)))
  filter_upwards [h'] with N hN
  obtain ⟨hb, hN1⟩ := hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hl0 : 0 < Real.log N := Real.log_pos hN1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hl0, abs_of_pos (by positivity), one_mul] at hb
  have h3 : Real.log N ^ 3 ≤ ((N : ℝ) ^ (1 / 6 : ℝ)) ^ 3 := pow_le_pow_left₀ hl0.le hb 3
  have h4 : ((N : ℝ) ^ (1 / 6 : ℝ)) ^ 3 = Real.sqrt N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Real.sqrt_eq_rpow]; norm_num
  rw [h4] at h3
  rw [le_div_iff₀ (by positivity)]
  have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

/-- **Goldston's Corollary 1 under RH on `N^c ≤ K ≤ √N`, `c > 2/21`**, CONDITIONAL ON the cited
Corollary 1 itself, whose hypothesis `J = o(K² N)` is now a theorem under RH: the number of
Goldbach representations in `[N, N + K]` is asymptotic to `K N/log² N`. -/
theorem corollary1_rh (hRH : RiemannHypothesis) (hC1 : Corollary1) {c : ℝ} (hc : 2 / 21 < c)
    (K : ℕ → ℕ) (hK : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ K N ∧ K N * K N ≤ N) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) / ((K N : ℝ) * N / Real.log N ^ 2))
      atTop (nhds 1) := by
  refine hC1 K ?_ (jg_little_o hRH hc K hK)
  filter_upwards [hK, eventually_sqrt_le, eventually_ge_atTop 1] with N hN hs hN1
  obtain ⟨hcK, hKN⟩ := hN
  have hNc : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow (by exact_mod_cast hN1) (by linarith)
  have hK1 : (1 : ℝ) ≤ K N := hNc.trans hcK
  refine ⟨by exact_mod_cast hK1, le_trans ?_ hs⟩
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have : ((K N * K N : ℕ) : ℝ) ≤ N := by exact_mod_cast hKN
  push_cast at this; nlinarith

end LeanLab.GoldbachGaps.Goldston1990
