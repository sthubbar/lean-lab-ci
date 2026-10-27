/-
P0030, Goldston 1990, unit U-6365, track T1, CLOUD 20261020T1125Z-cloud41, 2026-10-20.
Corollary 2 under RH on the range of `corollary1_rh_full`: for `log² N = o(K)` and
`64 K² ≤ N`, eventually at least `c K` of the `n ∈ [N, N + K]` are sums of two primes.
Goldston's route: Cauchy's inequality, display 14, the sieve bound `r(n) ≪ 𝔖(n) n/log² n`,
here SchnirelmannGoldbach `S1_sieve_upper` with `singProd`, and the short interval mean
square, display 26, `Σ_{N ≤ n ≤ N+K} singProd(n)² ≤ C (K + 1) + (1 + log(N + K))²`, proved
here by the method of SchnirelmannGoldbach/S2.lean with `K/d + 1` multiples of `d`.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.GoldbachGaps.Goldston1990Cor1Full
import LeanLab.SchnirelmannGoldbach.Discharged

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Finset Filter
open LeanLab.SchnirelmannGoldbach (singProd singProd_nonneg singProd_le_sum_divisors g g_nonneg
  g_summable g_mul_bound S1_sieve_upper)

/-- Multiples of `d ≥ 1` in `[N, N + K]`, `N ≥ 1`: at most `(K + 1)/d + 1`. -/
theorem card_dvd_Icc (N K d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) :
    (#{n ∈ Icc N (N + K) | d ∣ n} : ℝ) ≤ (K + 1) / d + 1 := by
  have hU : (Ioc 0 (N + K)).filter (fun n => d ∣ n)
      = (Ioc 0 (N - 1)).filter (fun n => d ∣ n) ∪ (Icc N (N + K)).filter (fun n => d ∣ n) := by
    ext n; simp only [mem_filter, mem_union, mem_Ioc, mem_Icc]; omega
  have hdisj : Disjoint ((Ioc 0 (N - 1)).filter (fun n => d ∣ n))
      ((Icc N (N + K)).filter (fun n => d ∣ n)) :=
    Finset.disjoint_left.mpr (fun n h1 h2 => by
      simp only [mem_filter, mem_Ioc, mem_Icc] at h1 h2; omega)
  have hc := card_union_of_disjoint hdisj
  rw [← hU, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hc
  have hC : #{n ∈ Icc N (N + K) | d ∣ n} = (N + K) / d - (N - 1) / d := by omega
  rw [hC]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hle : (N - 1) / d ≤ (N + K) / d := Nat.div_le_div_right (by omega)
  rw [Nat.cast_sub hle]
  have h1 : ((N + K) / d : ℕ) ≤ ((N + K : ℕ) : ℝ) / d := Nat.cast_div_le
  have h2 : ((N - 1 : ℕ) : ℝ) / d - 1 < ((N - 1) / d : ℕ) := by
    have := Nat.lt_div_mul_add (a := N - 1) hd
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hd']
    have : ((N - 1 : ℕ) : ℝ) < (((N - 1) / d : ℕ) : ℝ) * d + d := by
      have h := Nat.lt_div_mul_add (a := N - 1) hd
      exact_mod_cast h
    linarith
  have h3 : ((N + K : ℕ) : ℝ) = ((N - 1 : ℕ) : ℝ) + (K + 1) := by
    push_cast [Nat.cast_sub hN]; ring
  rw [h3, add_div] at h1
  linarith

/-- Display 26, Goldston's estimate: the mean square of `singProd` on a short interval. -/
theorem singProd_sq_Icc (N K : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Icc N (N + K), singProd n ^ 2
      ≤ (K + 1) * (∑' d, g d) ^ 2 + (1 + Real.log (N + K)) ^ 2 := by
  set M := N + K with hM
  have hM1 : 1 ≤ M := by omega
  set D := Icc 1 M with hD
  have key : ∀ n ∈ Icc N M, singProd n ^ 2 ≤
      ∑ d1 ∈ D, ∑ d2 ∈ D,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) := by
    intro n hn
    rw [mem_Icc] at hn
    have hsum : ∑ d ∈ n.divisors, 1 / (d : ℝ) =
        ∑ d ∈ D, (if d ∣ n then 1 / (d : ℝ) else 0) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext d
      simp only [Nat.mem_divisors, mem_filter, hD, mem_Icc]
      constructor
      · rintro ⟨hd, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hn.2⟩, hd⟩
      · rintro ⟨-, hd⟩; exact ⟨hd, by omega⟩
    rw [← Finset.sum_mul_sum, ← sq, ← hsum]
    gcongr
    · exact singProd_nonneg n
    · exact singProd_le_sum_divisors n (by omega)
  have pair : ∀ d1 ∈ D, ∀ d2 ∈ D,
      ∑ n ∈ Icc N M, (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0)
        ≤ (K + 1) * (g d1 * g d2) + 1 / (d1 : ℝ) * (1 / d2) := by
    intro d1 hd1 d2 hd2
    have h1 : 1 ≤ d1 := (mem_Icc.mp hd1).1
    have h2 : 1 ≤ d2 := (mem_Icc.mp hd2).1
    have hd1' : (0 : ℝ) < d1 := by exact_mod_cast h1
    have hd2' : (0 : ℝ) < d2 := by exact_mod_cast h2
    -- bound by the multiples of the larger of d1, d2
    have hb : ∀ a b : ℕ, 1 ≤ a → a ≤ b →
        ∑ n ∈ Icc N M, (if a ∣ n then 1 / (a : ℝ) else 0) * (if b ∣ n then 1 / (b : ℝ) else 0)
          ≤ (K + 1) * (g a * g b) + 1 / (a : ℝ) * (1 / b) := by
      intro a b ha hab
      have ha' : (0 : ℝ) < a := by exact_mod_cast ha
      have hb' : (0 : ℝ) < b := by exact_mod_cast (le_trans ha hab)
      calc ∑ n ∈ Icc N M, (if a ∣ n then 1 / (a : ℝ) else 0) * (if b ∣ n then 1 / (b : ℝ) else 0)
          ≤ ∑ n ∈ Icc N M, 1 / (a : ℝ) * (if b ∣ n then 1 / (b : ℝ) else 0) := by
            apply Finset.sum_le_sum; intro n _
            apply mul_le_mul_of_nonneg_right
            · split_ifs
              · exact le_rfl
              · positivity
            · split_ifs <;> positivity
        _ = 1 / (a : ℝ) * (1 / b) * #{n ∈ Icc N M | b ∣ n} := by
            rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
              Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 1 / (a : ℝ) * (1 / b) * ((K + 1) / b + 1) := by
            gcongr; exact card_dvd_Icc N K b hN (le_trans ha hab)
        _ = (K + 1) * (1 / ((a : ℝ) * b * b)) + 1 / (a : ℝ) * (1 / b) := by
            field_simp
        _ ≤ (K + 1) * (g a * g b) + 1 / (a : ℝ) * (1 / b) := by
            gcongr; exact g_mul_bound a b ha hab
    rcases le_total d1 d2 with h | h
    · exact hb d1 d2 h1 h
    · have := hb d2 d1 h2 h
      simp_rw [mul_comm (if d2 ∣ _ then _ else _)] at this
      calc _ ≤ (K + 1) * (g d2 * g d1) + 1 / (d2 : ℝ) * (1 / d1) := this
        _ = _ := by ring
  have hH : ∑ d ∈ D, 1 / (d : ℝ) ≤ 1 + Real.log M := by
    have := harmonic_le_one_add_log M
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    simpa [hD, one_div] using this
  calc ∑ n ∈ Icc N M, singProd n ^ 2
      ≤ ∑ n ∈ Icc N M, ∑ d1 ∈ D, ∑ d2 ∈ D,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) :=
        Finset.sum_le_sum key
    _ = ∑ d1 ∈ D, ∑ d2 ∈ D, ∑ n ∈ Icc N M,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro _ _; rw [Finset.sum_comm]
    _ ≤ ∑ d1 ∈ D, ∑ d2 ∈ D, ((K + 1) * (g d1 * g d2) + 1 / (d1 : ℝ) * (1 / d2)) := by
        apply Finset.sum_le_sum; intro d1 hd1; apply Finset.sum_le_sum; intro d2 hd2
        exact pair d1 hd1 d2 hd2
    _ = (K + 1) * (∑ d ∈ D, g d) ^ 2 + (∑ d ∈ D, 1 / (d : ℝ)) ^ 2 := by
        rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro _ _
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ (K + 1) * (∑' d, g d) ^ 2 + (1 + Real.log M) ^ 2 := by
        have hg0 : 0 ≤ ∑ d ∈ D, g d := Finset.sum_nonneg (fun d _ => g_nonneg d)
        have hg1 : ∑ d ∈ D, g d ≤ ∑' d, g d := g_summable.sum_le_tsum _ (fun d _ => g_nonneg d)
        have hh0 : 0 ≤ ∑ d ∈ D, 1 / (d : ℝ) := Finset.sum_nonneg (fun d _ => by positivity)
        gcongr
    _ = _ := by rw [hM]; push_cast; ring

/-- Goldston's Corollary 2 under RH, on the range of `corollary1_rh_full`: if `log² N = o(K)` and
`64 K² ≤ N`, a positive proportion of `[N, N + K]` are sums of two primes. -/
theorem corollary2_rh (hRH : RiemannHypothesis) (K : ℕ → ℕ)
    (hlog : Tendsto (fun N : ℕ => Real.log N ^ 2 / K N) atTop (nhds 0))
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ 64 * (K N * K N) ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * K N ≤ (((Icc N (N + K N)).filter (fun n => 1 ≤ rg n)).card : ℝ) := by
  obtain ⟨C, hC⟩ := S1_sieve_upper
  set C0 := max C 1 with hC0
  have hC01 : 1 ≤ C0 := le_max_right _ _
  set G := (∑' d, g d) ^ 2 with hG
  have hG0 : 0 ≤ G := sq_nonneg _
  refine ⟨1 / (16 * C0 ^ 2 * (2 * G + 9)), by positivity, ?_⟩
  have h1 := corollary1_rh_full hRH K hlog hK
  have tN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have eL : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tN).eventually_ge_atTop 1
  have eN : ∀ᶠ N : ℕ in atTop, 3 ≤ N := eventually_ge_atTop 3
  have eHalf : ∀ᶠ N : ℕ in atTop, 1 / 2 ≤
      (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) / ((K N : ℝ) * N / Real.log N ^ 2) :=
    h1.eventually (Ici_mem_nhds (by norm_num))
  have eKL : ∀ᶠ N : ℕ in atTop, Real.log N ^ 2 / K N ≤ 1 :=
    hlog.eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [eL, eN, eHalf, eKL, hK] with N hL hN3 hHalf hKL hKN
  obtain ⟨hK1, hK64⟩ := hKN
  set k := K N with hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hK1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkN : k ≤ N := by nlinarith
  set L := Real.log N with hLdef
  have hL2 : L ^ 2 ≤ k := by
    rw [div_le_one hk0] at hKL; exact hKL
  set I := Icc N (N + k) with hI
  set S := I.filter (fun n => 1 ≤ rg n) with hS
  -- the sieve bound on I
  have hr : ∀ n ∈ I, (rg n : ℝ) ≤ 2 * C0 * N / L ^ 2 * singProd n := by
    intro n hn
    rw [hI, mem_Icc] at hn
    have hn3 : 3 ≤ n := by omega
    have hrr : (rg n : ℝ) ≤ C * n / Real.log n ^ 2 * singProd n := hC n hn3
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlogn : L ≤ Real.log n := Real.log_le_log hN0 (by exact_mod_cast hn.1)
    have hL0 : 0 < L := by linarith
    have hsp := singProd_nonneg n
    have hn2 : (n : ℝ) ≤ 2 * N := by
      have : (n : ℝ) ≤ N + k := by exact_mod_cast hn.2
      have : (k : ℝ) ≤ N := by exact_mod_cast hkN
      linarith
    have a1 : C * n / Real.log n ^ 2 * singProd n ≤ C0 * n / Real.log n ^ 2 * singProd n := by
      have : 0 ≤ (n : ℝ) / Real.log n ^ 2 * singProd n := by positivity
      have hc : C ≤ C0 := le_max_left _ _
      calc C * n / Real.log n ^ 2 * singProd n = C * ((n : ℝ) / Real.log n ^ 2 * singProd n) := by ring
        _ ≤ C0 * ((n : ℝ) / Real.log n ^ 2 * singProd n) := mul_le_mul_of_nonneg_right hc this
        _ = _ := by ring
    have a2 : (n : ℝ) / Real.log n ^ 2 ≤ 2 * N / L ^ 2 := by
      have hl2 : L ^ 2 ≤ Real.log n ^ 2 := pow_le_pow_left₀ hL0.le hlogn 2
      calc (n : ℝ) / Real.log n ^ 2 ≤ n / L ^ 2 := div_le_div_of_nonneg_left hnpos.le (by positivity) hl2
        _ ≤ 2 * N / L ^ 2 := div_le_div_of_nonneg_right hn2 (by positivity)
    calc (rg n : ℝ) ≤ C0 * n / Real.log n ^ 2 * singProd n := hrr.trans a1
      _ = C0 * ((n : ℝ) / Real.log n ^ 2) * singProd n := by ring
      _ ≤ C0 * (2 * N / L ^ 2) * singProd n := by gcongr
      _ = 2 * C0 * N / L ^ 2 * singProd n := by ring
  -- display 26 on I
  have h26 := singProd_sq_Icc N k (by omega)
  have hlog2 : (1 + Real.log ((N : ℝ) + k)) ^ 2 ≤ 9 * k := by
    have hNk : (N : ℝ) + k ≤ N * N := by
      have : (k : ℝ) ≤ N := by exact_mod_cast hkN
      have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
      nlinarith
    have hl : Real.log ((N : ℝ) + k) ≤ 2 * L := by
      calc Real.log ((N : ℝ) + k) ≤ Real.log ((N : ℝ) * N) := Real.log_le_log (by positivity) hNk
        _ = 2 * L := by rw [Real.log_mul hN0.ne' hN0.ne']; ring
    have h0 : 0 ≤ Real.log ((N : ℝ) + k) := Real.log_nonneg (by
      have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith)
    nlinarith
  have hsq : ∑ n ∈ I, singProd n ^ 2 ≤ (2 * G + 9) * k := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hK1
    have : ((k : ℝ) + 1) * G ≤ 2 * G * k := by nlinarith
    push_cast at h26
    linarith
  have hr2 : ∑ n ∈ I, (rg n : ℝ) ^ 2 ≤ (2 * C0 * N / L ^ 2) ^ 2 * ((2 * G + 9) * k) := by
    calc ∑ n ∈ I, (rg n : ℝ) ^ 2 ≤ ∑ n ∈ I, (2 * C0 * N / L ^ 2) ^ 2 * singProd n ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [← mul_pow]
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hr n hn) 2
      _ = (2 * C0 * N / L ^ 2) ^ 2 * ∑ n ∈ I, singProd n ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  -- Cauchy's inequality, display 14
  have hsumS : ∑ n ∈ I, (rg n : ℝ) = ∑ n ∈ S, (rg n : ℝ) := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with h
    · rfl
    · have : rg n = 0 := by omega
      simp [this]
  have hcs : (∑ n ∈ S, (rg n : ℝ)) ^ 2 ≤ (S.card : ℝ) * ∑ n ∈ S, (rg n : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hSI : ∑ n ∈ S, (rg n : ℝ) ^ 2 ≤ ∑ n ∈ I, (rg n : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  -- the lower bound from Corollary 1
  have hL0 : 0 < L := by linarith
  have hden : 0 < (k : ℝ) * N / L ^ 2 := by positivity
  have hlow : (k : ℝ) * N / L ^ 2 / 2 ≤ ∑ n ∈ I, (rg n : ℝ) := by
    rw [le_div_iff₀ hden] at hHalf; linarith
  set A := (k : ℝ) * N / L ^ 2 with hA
  set B := (2 * C0 * N / L ^ 2) ^ 2 * ((2 * G + 9) * k) with hB
  have hB0 : 0 < B := by positivity
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have key : (A / 2) ^ 2 ≤ S.card * B := by
    have h1 : (A / 2) ^ 2 ≤ (∑ n ∈ I, (rg n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    rw [hsumS] at h1
    calc (A / 2) ^ 2 ≤ (S.card : ℝ) * ∑ n ∈ S, (rg n : ℝ) ^ 2 := h1.trans hcs
      _ ≤ S.card * B := mul_le_mul_of_nonneg_left (hSI.trans hr2) hS0
  have e : (A / 2) ^ 2 = (1 / (16 * C0 ^ 2 * (2 * G + 9)) * k) * B := by
    rw [hA, hB]; field_simp; ring
  rw [e] at key
  exact le_of_mul_le_mul_right key hB0

end LeanLab.GoldbachGaps.Goldston1990
