import Mathlib
import LeanLab.GoldbachGaps.Goldston1990Main
import LeanLab.GoldbachGaps.Goldston1990Cor2
import LeanLab.SchnirelmannGoldbach.Discharged

namespace LeanLab.GoldbachGaps.DecompJ610
open Real Finset Filter Topology
open LeanLab.GoldbachGaps.Goldston1990
open LeanLab.SchnirelmannGoldbach

/-- LEAF p. 292: Corollary 1, display 7 -/
theorem leaf_corollary1 : Corollary1 := sorry

/-- LEAF p. 292: Cauchy's inequality for rg on [N, N+K] -/
theorem leaf_cauchy_rg (N K : ℕ) :
    (∑ n ∈ Icc N (N + K), (rg n : ℝ)) ^ 2 ≤
    (((Icc N (N + K)).filter (fun n => 1 ≤ rg n)).card : ℝ) *
    ∑ n ∈ Icc N (N + K), (rg n : ℝ) ^ 2 := by
  let S := (Icc N (N + K)).filter (fun n => 1 ≤ rg n)
  have h_eq : ∑ n ∈ Icc N (N + K), (rg n : ℝ) = ∑ n ∈ S, (rg n : ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro x hx
    split_ifs with h
    · rfl
    · have : rg x = 0 := by omega
      rw [this, Nat.cast_zero]
  rw [h_eq]
  have := sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun n => (rg n : ℝ))
  simp only [one_mul, sum_const, nsmul_eq_mul] at this
  have hs_eq : (S.card : ℝ) * 1 ^ 2 = (S.card : ℝ) := by ring
  rw [hs_eq] at this
  refine le_trans this ?_
  have h_le : ∑ i ∈ S, (rg i : ℝ) ^ 2 ≤ ∑ n ∈ Icc N (N + K), (rg n : ℝ) ^ 2 := by
    refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_
    intro n _ _
    exact sq_nonneg _
  exact mul_le_mul_of_nonneg_left h_le (Nat.cast_nonneg _)

/-- LEAF p. 292: Lower bound for sum of rg from Corollary 1 -/
theorem leaf_sum_rg_lower_bound (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hj : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    ∀ᶠ N : ℕ in atTop, 1 / 2 * K N * N / Real.log N ^ 2 ≤ ∑ n ∈ Icc N (N + K N), (rg n : ℝ) := sorry

/-- LEAF p. 293: Sieve bound pointwise on [N, N+K] -/
theorem leaf_rg_le_singProd (C : ℝ) (_hC : 0 < C) (N K : ℕ) (n : ℕ) (_hn : n ∈ Icc N (N + K))
    (_hN : 3 ≤ N) (_hKN : K ≤ N) :
    (rg n : ℝ) ≤ C * n / Real.log n ^ 2 * singProd n →
    (rg n : ℝ) ≤ 2 * C * N / Real.log N ^ 2 * singProd n := by
  intro h
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp _hn
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast _hN
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h3 : 3 ≤ n := le_trans _hN hn1
    exact_mod_cast (by omega : 0 < n)
  have hnN : (n : ℝ) ≤ 2 * N := by
    have h2 : n ≤ 2 * N := by omega
    exact_mod_cast h2
  have hLN : 0 < Real.log (N : ℝ) := by
    have : (1 : ℝ) < (N : ℝ) := by
      have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast _hN
      linarith
    exact Real.log_pos this
  have hLn : Real.log (N : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hNpos (by exact_mod_cast hn1)
  have hsq : Real.log (N : ℝ) ^ 2 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  have hkey : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ 2 * N / Real.log (N : ℝ) ^ 2 := by
    have h1 : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) / Real.log (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hnpos.le (by positivity) hsq
    have h2 : (n : ℝ) / Real.log (N : ℝ) ^ 2 ≤ (2 * N) / Real.log (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hnN (by positivity)
    linarith
  have hsp : 0 ≤ singProd n := singProd_nonneg n
  calc (rg n : ℝ) ≤ C * n / Real.log (n : ℝ) ^ 2 * singProd n := h
    _ = C * ((n : ℝ) / Real.log (n : ℝ) ^ 2) * singProd n := by ring
    _ ≤ C * ((2 * N) / Real.log (N : ℝ) ^ 2) * singProd n := by
        refine mul_le_mul_of_nonneg_right ?_ hsp
        exact mul_le_mul_of_nonneg_left hkey _hC.le
    _ = 2 * C * N / Real.log (N : ℝ) ^ 2 * singProd n := by ring

/-- LEAF p. 293: Sieve bound pointwise square on [N, N+K] -/
theorem leaf_rg_sq_le_singProd (C : ℝ) (_hC : 0 < C) (N K : ℕ) (n : ℕ) (_hn : n ∈ Icc N (N + K))
    (_hN : 3 ≤ N) (_hKN : K ≤ N) :
    (rg n : ℝ) ≤ 2 * C * N / Real.log N ^ 2 * singProd n →
    (rg n : ℝ) ^ 2 ≤ 4 * C ^ 2 * (N : ℝ) ^ 2 / Real.log N ^ 4 * singProd n ^ 2 := by
  intro h
  have h1 : 0 ≤ (rg n : ℝ) := Nat.cast_nonneg _
  have h4 := mul_self_le_mul_self h1 h
  have e : (2 * C * N / Real.log N ^ 2 * singProd n) * (2 * C * N / Real.log N ^ 2 * singProd n) = 4 * C ^ 2 * (N : ℝ) ^ 2 / Real.log N ^ 4 * singProd n ^ 2 := by ring
  have e2 : (rg n : ℝ) * (rg n : ℝ) = (rg n : ℝ) ^ 2 := by ring
  rw [e2] at h4
  rwa [e] at h4

/-- LEAF p. 293: Sieve bound sum on [N, N+K] -/
theorem leaf_sum_rg_sq_le (C : ℝ) (_hC : 0 < C) (N K : ℕ) (_hN : 3 ≤ N) (_hKN : K ≤ N)
    (h_pointwise : ∀ n ∈ Icc N (N + K), (rg n : ℝ) ^ 2 ≤ 4 * C ^ 2 * (N : ℝ) ^ 2 / Real.log N ^ 4 * singProd n ^ 2) :
    ∑ n ∈ Icc N (N + K), (rg n : ℝ) ^ 2 ≤
    4 * C ^ 2 * (N : ℝ) ^ 2 / Real.log N ^ 4 * ∑ n ∈ Icc N (N + K), singProd n ^ 2 := by
  have := sum_le_sum h_pointwise
  rw [← Finset.mul_sum] at this
  exact this

/-- LEAF p. 293: Mean square of singProd bounded by K -/
theorem leaf_singProd_sq_bound (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, Real.log N ^ 2 ≤ K N) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    ∑ n ∈ Icc N (N + K N), singProd n ^ 2 ≤ C * K N := by
  have hS0 : 0 ≤ ∑' d, g d := tsum_nonneg (fun d => g_nonneg d)
  refine ⟨2 * (∑' d, g d) ^ 2 + 16, by positivity, ?_⟩
  have eL : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hlog1 : ∀ᶠ N : ℕ in atTop, Real.log (1 + (K N : ℝ)) ≤ 2 * Real.sqrt (K N) := by
    filter_upwards [hK, eL] with N hKN hL
    have hk1 : (1 : ℝ) ≤ (K N : ℝ) := by nlinarith
    have h1 : Real.log (1 + (K N : ℝ)) = 2 * Real.log (Real.sqrt (1 + (K N : ℝ))) := by
      rw [Real.log_sqrt (by positivity)]; ring
    have h2 : Real.log (Real.sqrt (1 + (K N : ℝ))) ≤ Real.sqrt (1 + (K N : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.sqrt (1 + (K N : ℝ)) - 1 ≤ Real.sqrt (K N) := by
      have hs1 : (1 : ℝ) ≤ Real.sqrt (1 + (K N : ℝ)) :=
        Real.one_le_sqrt.mpr (by linarith)
      have hsq : (Real.sqrt (1 + (K N : ℝ)) - 1) ^ 2 ≤ (K N : ℝ) := by
        have hsp := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + (K N : ℝ) by positivity)
        nlinarith
      have hs0 : 0 ≤ Real.sqrt (1 + (K N : ℝ)) - 1 := by linarith
      calc Real.sqrt (1 + (K N : ℝ)) - 1
          = Real.sqrt ((Real.sqrt (1 + (K N : ℝ)) - 1) ^ 2) := by
            rw [Real.sqrt_sq hs0]
        _ ≤ Real.sqrt (K N) := Real.sqrt_le_sqrt hsq
    linarith
  filter_upwards [hK, eL, hlog1, eventually_ge_atTop 1] with N hKN hL hlogK hN
  have hk_ge : Real.log ↑N ^ 2 ≤ (K N : ℝ) := hKN
  have hk1 : (1 : ℝ) ≤ (K N : ℝ) := by nlinarith
  have hN1 : 1 ≤ N := hN
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hkN0 : (0 : ℝ) ≤ (K N : ℝ) := Nat.cast_nonneg _
  have hkey := singProd_sq_Icc N (K N) hN1
  have hLN0 : 0 ≤ Real.log N := by linarith
  have hsK : Real.log N ≤ Real.sqrt ((K N : ℝ)) :=
    (Real.le_sqrt hLN0 (by positivity)).mpr hk_ge
  have hsplit : Real.log ((N : ℝ) + K N) ≤ Real.log N + Real.log (1 + (K N : ℝ)) := by
    have hpos : (0 : ℝ) < (N : ℝ) := by linarith
    have h1 : (0 : ℝ) < 1 + (K N : ℝ) := by positivity
    have hle : (N : ℝ) + K N ≤ (N : ℝ) * (1 + K N) := by nlinarith
    calc Real.log ((N : ℝ) + K N) ≤ Real.log ((N : ℝ) * (1 + K N)) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log N + Real.log (1 + (K N : ℝ)) := Real.log_mul hpos.ne' h1.ne'
  have hbig : (1 + Real.log ((N : ℝ) + K N)) ^ 2 ≤ 16 * K N := by
    have ht0 : 0 ≤ Real.sqrt (K N) := Real.sqrt_nonneg _
    have htsq : Real.sqrt (K N) ^ 2 = (K N : ℝ) := Real.sq_sqrt (by positivity)
    have htK : Real.sqrt (K N) ≤ (K N : ℝ) := by
      have h1 : 1 ≤ Real.sqrt (K N) := Real.one_le_sqrt.mpr hk1
      have h2 : Real.sqrt (K N) ≤ Real.sqrt (K N) * Real.sqrt (K N) := by
        simpa using mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (K N))
      nlinarith [h2, htsq]
    have hlog0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + K N) :=
      Real.log_nonneg (by linarith)
    have h0 : (0 : ℝ) ≤ 1 + Real.log ((N : ℝ) + K N) := by linarith
    have h1 : 1 + Real.log ((N : ℝ) + K N) ≤ 1 + 3 * Real.sqrt (K N) := by linarith
    have hprod := mul_self_le_mul_self h0 h1
    nlinarith [hprod]
  have hKpos : (0 : ℝ) < (K N : ℝ) := by linarith
  have hsum1 : (K N + 1) * (∑' d, g d) ^ 2 ≤ 2 * (K N : ℝ) * (∑' d, g d) ^ 2 := by
    have : ((K N : ℝ) + 1) ≤ 2 * (K N : ℝ) := by linarith
    calc ((K N : ℝ) + 1) * (∑' d, g d) ^ 2
        ≤ (2 * (K N : ℝ)) * (∑' d, g d) ^ 2 := by
          apply mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 * (K N : ℝ) * (∑' d, g d) ^ 2 := by ring
  nlinarith [hkey, hsum1, hbig]

/-- LEAF p. 293: Sum of rg^2 bounded by K * N^2 / log^4 N -/
theorem leaf_sum_rg_sq_bound_K (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, Real.log N ^ 2 ≤ K N ∧ K N ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    ∑ n ∈ Icc N (N + K N), (rg n : ℝ) ^ 2 ≤ C * K N * (N : ℝ) ^ 2 / Real.log N ^ 4 := by
  obtain ⟨C₁, hC₁⟩ := S1_sieve_upper
  set C₁' := max C₁ 1 with hC₁'def
  have hC₁pos : 0 < C₁' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC1le : C₁ ≤ C₁' := le_max_left _ _
  obtain ⟨C₂, hC₂pos, hC₂⟩ := leaf_singProd_sq_bound K (hK.mono fun N h => h.1)
  refine ⟨4 * C₁' ^ 2 * C₂, by positivity, ?_⟩
  filter_upwards [hK, hC₂, eventually_ge_atTop 3] with N hKN hS hN3
  obtain ⟨hklog, hkK⟩ := hKN
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    exact this)
  have hpt : ∀ n ∈ Icc N (N + K N), (rg n : ℝ) ^ 2 ≤
      4 * C₁' ^ 2 * (N : ℝ) ^ 2 / Real.log N ^ 4 * singProd n ^ 2 := by
    intro n hn
    obtain ⟨hn1, -⟩ := Finset.mem_Icc.mp hn
    have hn3 : 3 ≤ n := le_trans hN3 hn1
    have hs1 : (rg n : ℝ) ≤ C₁ * n / Real.log n ^ 2 * singProd n := hC₁ n hn3
    have hq : (0 : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 :=
      div_nonneg (Nat.cast_nonneg _) (by positivity)
    have hs2 : (rg n : ℝ) ≤ C₁' * n / Real.log n ^ 2 * singProd n := by
      refine le_trans hs1 ?_
      have hm : C₁ * ((n : ℝ) / Real.log (n : ℝ) ^ 2) ≤ C₁' * ((n : ℝ) / Real.log (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hC1le hq
      have e1 : C₁ * n / Real.log (n : ℝ) ^ 2 = C₁ * ((n : ℝ) / Real.log (n : ℝ) ^ 2) := by ring
      have e2 : C₁' * n / Real.log (n : ℝ) ^ 2 = C₁' * ((n : ℝ) / Real.log (n : ℝ) ^ 2) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hm (singProd_nonneg n)
    have hs3 := leaf_rg_le_singProd C₁' hC₁pos N (K N) n hn hN3 hkK hs2
    exact leaf_rg_sq_le_singProd C₁' hC₁pos N (K N) n hn hN3 hkK hs3
  have h1 := leaf_sum_rg_sq_le C₁' hC₁pos N (K N) hN3 hkK hpt
  have h2 : 4 * C₁' ^ 2 * (N : ℝ) ^ 2 / Real.log N ^ 4 *
      (∑ n ∈ Icc N (N + K N), singProd n ^ 2) ≤
      4 * C₁' ^ 2 * (N : ℝ) ^ 2 / Real.log N ^ 4 * (C₂ * K N) :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  refine le_trans h1 (le_trans h2 (le_of_eq ?_))
  ring

/-- LEAF p. 293: Assembly of Corollary 2 -/
theorem leaf_assembly_corollary2 : Corollary2 := sorry

theorem assembly_corollary2 : Corollary2 := leaf_assembly_corollary2

end LeanLab.GoldbachGaps.DecompJ610
