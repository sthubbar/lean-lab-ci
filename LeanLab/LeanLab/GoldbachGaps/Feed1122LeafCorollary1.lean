/-
Split of `leaf_corollary1` of `LeanLab.GoldbachGaps.DecompJ610`, P0030 D. A. Goldston, Linnik's
theorem on Goldbach numbers in short intervals, Glasgow Math. J. 32 (1990) 285-297, Corollary 1,
display 7, page 292.

Corollary 1 says: if `J(N, K) = o(K² N)` then `Σ_{N ≤ n ≤ N + K} r(n) ~ K N / log² N`. Goldston's
proof has two parts:

* LEAF 1, the weighted count: `Σ_{N ≤ n ≤ N + K} R(n) ~ K N`, from the Theorem, display 6, by
  differencing the Fejér sum, display 7 and the lines after it.
* LEAF 2, the unweighting: `R(n) ≤ r(n) log² n`, and the pairs with a prime below
  `y = N / log³ N` number at most `2 (K + 1) y`, so the asymptotic for `R` gives the one for `r`
  with `log² N` in the denominator.

`leaf_corollary1_of_leaves` has the statement of `leaf_corollary1`, which is `Corollary1`, proved from
the two leaves alone.

AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.GoldbachGaps.Goldston1990Main
import LeanLab.GoldbachGaps.Goldston1990Cor1

namespace LeanLab.GoldbachGaps.Feed1122Cor1
open Real Finset Filter Topology
open LeanLab.GoldbachGaps.Goldston1990

/-- LEAF: Goldston page 292, display 7 and the differencing after it: under the Theorem's range
`1 ≤ K ≤ N / log³ N` and `J(N, K) = o(K² N)`, the weighted Goldbach count over the printed
interval satisfies `Σ_{N ≤ n ≤ N + K} R(n) ~ K N`. HARD: the Fejér sum of display 6 is centred
at `N` with half width `K`, the printed interval is centred at `N + K/2` with half width `K/2`;
U-1613 suggests the trapezoid route with Cauchy's inequality and the pair sieve bound
`J(N, h) ≪ h² N`, see `DecompJ205.leaf_relabel`. -/
theorem leaf_sum_Rg_interval_asymp (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hJ : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), Rg n) / ((K N : ℝ) * N)) atTop (nhds 1) := by
  sorry

/-- Lower comparison on `[N, N + K]`: `R(n) ≤ r(n) log² (N + K)` summed, Goldston page 292. -/
theorem isum_ge (N K : ℕ) :
    (∑ n ∈ Icc N (N + K), Rg n) / Real.log ((N : ℝ) + K) ^ 2 ≤ ∑ n ∈ Icc N (N + K), (rg n : ℝ) := by
  rcases eq_or_lt_of_le (sq_nonneg (Real.log ((N : ℝ) + K))) with h0 | hpos
  · rw [← h0, div_zero]; exact sum_nonneg fun _ _ => Nat.cast_nonneg _
  rw [div_le_iff₀ hpos, sum_mul]
  apply sum_le_sum; intro n hn
  have hn' := mem_Icc.mp hn
  have := Rg_le_rg (n := n) (M := N + K) hn'.2
  push_cast at this
  exact this

/-- Upper comparison on `[N, N + K]`: `r(n) ≤ R(n)/log² y + 2(y + 1)` summed over the `K + 1`
integers, Goldston page 292. -/
theorem isum_le (N K : ℕ) {y : ℝ} (hy : 1 < y) :
    ∑ n ∈ Icc N (N + K), (rg n : ℝ) ≤
      (∑ n ∈ Icc N (N + K), Rg n) / Real.log y ^ 2 + (K + 1) * (2 * (y + 1)) := by
  calc ∑ n ∈ Icc N (N + K), (rg n : ℝ)
      ≤ ∑ n ∈ Icc N (N + K), (Rg n / Real.log y ^ 2 + 2 * (y + 1)) :=
        sum_le_sum fun n _ => rg_le_Rg _ hy
    _ = _ := by
      rw [sum_add_distrib, ← sum_div, sum_const, Nat.card_Icc, show N + K + 1 - N = K + 1 by omega,
        nsmul_eq_mul]
      push_cast; ring

set_option maxHeartbeats 1000000 in
/-- Goldston page 292, the passage from `R` to `r` in Corollary 1: for `K` in the Theorem's
range, `Σ_{N ≤ n ≤ N + K} R(n) ~ K N` implies `Σ_{N ≤ n ≤ N + K} r(n) ~ K N / log² N`. Lower half:
`R(n) ≤ r(n) log² (N + K)` and `log (N + K) ~ log N`. Upper half: a pair with both primes above
`y = N / log³ N` has weight at least `log² y`, the other pairs number at most `2 (K + 1) π(y)`,
which is `o(K N / log² N)`, and `log y ~ log N`. Formerly a MEDIUM LEAF, PROVED by session S91 with the lemmas
`Rg_le_rg`, `rsumr_ge`, `rsumr_le` of `Goldston1990Cor1` do most of it. True for every `K ≥ 1`,
no growth of `K` needed. -/
theorem leaf_rg_of_Rg_interval (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hR : Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), Rg n) / ((K N : ℝ) * N)) atTop
      (nhds 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) / ((K N : ℝ) * N / Real.log N ^ 2))
      atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro δ0 hδ0
  set δ := min δ0 1 with hδdef
  have hδ : 0 < δ := lt_min hδ0 one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set ε := min (1 / 5 : ℝ) (δ / 10) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hδδ : δ ≤ δ0 := min_le_left _ _
  have hε5 : ε ≤ 1 / 5 := min_le_left _ _
  have hεδ : ε ≤ δ / 10 := min_le_right _ _
  rw [Metric.tendsto_atTop] at hR
  obtain ⟨A1, hA1⟩ := hR (δ / 4) (by positivity)
  have tL := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have eL : ∀ᶠ N : ℕ in atTop, max (max 1 (64 / ε ^ 2)) (max (8 / δ) (48 / δ)) ≤ Real.log N :=
    tL.eventually_ge_atTop _
  have t4 : Tendsto (fun N : ℕ => Real.log N ^ 4 / (1 * (N : ℝ) + 0)) atTop (nhds 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have e4 : ∀ᶠ N : ℕ in atTop, Real.log N ^ 4 / (1 * (N : ℝ) + 0) < δ / 48 :=
    t4.eventually (Iio_mem_nhds (by positivity))
  have eN : ∀ᶠ N : ℕ in atTop, A1 ≤ N := eventually_ge_atTop A1
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eL.and (e4.and (eN.and hK)))
  refine ⟨M, fun N hNM => ?_⟩
  obtain ⟨hLb, h4, hNA, hK1, hK3⟩ := hM N hNM
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLb
  have hL64 : 64 / ε ^ 2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLb
  have hL48 : 48 / δ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLb
  have hL0 : 0 < L := by linarith
  have hNpos : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso; rw [hLdef, h, Nat.cast_zero, Real.log_zero] at hL1; linarith
    · exact_mod_cast h
  have hkpos : (0 : ℝ) < K N := by exact_mod_cast hK1
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have hKN : (K N : ℝ) ≤ N := by
    refine hK3.trans ?_
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hR' := hA1 N hNA
  have hD : (0 : ℝ) < K N * N := by positivity
  rw [Real.dist_eq, abs_lt] at hR'
  have hRlo : (1 - δ / 4) * (K N * N) ≤ ∑ n ∈ Icc N (N + K N), Rg n := by
    have := hR'.1; rw [lt_sub_iff_add_lt, lt_div_iff₀ hD] at this; nlinarith
  have hRhi : ∑ n ∈ Icc N (N + K N), Rg n ≤ (1 + δ / 4) * (K N * N) := by
    have := hR'.2; rw [sub_lt_iff_lt_add, div_lt_iff₀ hD] at this; nlinarith
  have hL24' : 24 ≤ δ * L := by rw [div_le_iff₀ hδ] at hL48; linarith
  have hL24h : 24 ≤ δ / 2 * L := by rw [div_le_iff₀ hδ] at hL48; linarith
  have hR0 : 0 ≤ ∑ n ∈ Icc N (N + K N), Rg n := le_trans (by nlinarith) hRlo
  rw [show (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) / (K N * N / L ^ 2) =
      (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) * L ^ 2 / (K N * N) by field_simp]
  rw [Real.dist_eq, abs_lt]
  constructor
  · have hlog2 : Real.log ((N : ℝ) + K N) ≤ L + 1 := by
      have h2N : (N : ℝ) + K N ≤ 2 * N := by linarith
      have := Real.log_le_log (by positivity) h2N
      rw [Real.log_mul (by norm_num) hNpos.ne'] at this
      have : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    have hlog0 : 0 < Real.log ((N : ℝ) + K N) := by
      have hN1 : (1 : ℝ) < N := by
        by_contra h; push Not at h
        have : L ≤ 0 := by rw [hLdef]; exact Real.log_nonpos hNpos.le h
        linarith
      exact Real.log_pos (by linarith)
    have hge := isum_ge N (K N)
    have := cor1_lower hδ hδ1 hL1 hL24' hD hRlo hge hlog0 hlog2
    linarith
  · set y : ℝ := N / L ^ 4 with hydef
    have hL4 : 0 < L ^ 4 := by positivity
    have h4' : L ^ 4 / N < δ / 48 := by simpa using h4
    have h4'' : L ^ 4 < δ / 48 * N := by rwa [div_lt_iff₀ hNpos] at h4'
    have hy2 : 2 ≤ y := by
      rw [hydef, le_div_iff₀ hL4]; nlinarith
    have hy1 : 1 < y := by linarith
    have hlogy : (1 - ε) * L ≤ Real.log y := by
      rw [hydef, Real.log_div hNpos.ne' hL4.ne', Real.log_pow]
      have hll : Real.log L ≤ 2 * Real.sqrt L := LeanLab.GoldbachAverage.log_le_two_sqrt hL0
      have hL64' : 64 ≤ ε ^ 2 * L := by rw [div_le_iff₀ (by positivity)] at hL64; linarith
      have hsL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
      have hsq : 8 ≤ ε * Real.sqrt L := by
        have h0 : 0 ≤ ε * Real.sqrt L := by positivity
        nlinarith
      have : 8 * Real.sqrt L ≤ ε * L := by
        calc 8 * Real.sqrt L ≤ (ε * Real.sqrt L) * Real.sqrt L :=
              mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg L)
          _ = ε * L := by rw [mul_assoc, hsL]
      push_cast
      linarith
    have hle := isum_le N (K N) hy1
    have hE2 : (2 * K N + 1) * (2 * (y + 1)) * L ^ 2 ≤ δ / 2 / 4 * (2 * K N * N) :=
      cor1_E (by exact_mod_cast hK1) hNpos hL1 hL24h (by positivity)
        (by rw [hydef]; field_simp) (by linarith)
    have hy0 : 0 ≤ 2 * (y + 1) * L ^ 2 := by positivity
    have hE : ((K N : ℝ) + 1) * (2 * (y + 1)) * L ^ 2 ≤ δ / 4 * (K N * N) := by
      have : ((K N : ℝ) + 1) * (2 * (y + 1)) * L ^ 2 ≤ (2 * K N + 1) * (2 * (y + 1)) * L ^ 2 := by
        have h1 : (K N : ℝ) + 1 ≤ 2 * K N + 1 := by linarith
        nlinarith
      nlinarith
    have := cor1_upper hδ hδ1 hε hε5 hεδ hL0 hlogy hD hRhi hR0 hle hE
    linarith


/-- `leaf_corollary1` of `DecompJ610`, statement identical, `Corollary1`, from the two leaves. -/
theorem leaf_corollary1_of_leaves : Corollary1 := by
  intro K hK hJ
  exact leaf_rg_of_Rg_interval K hK (leaf_sum_Rg_interval_asymp K hK hJ)

end LeanLab.GoldbachGaps.Feed1122Cor1

#print axioms LeanLab.GoldbachGaps.Feed1122Cor1.leaf_corollary1_of_leaves
#print axioms LeanLab.GoldbachGaps.Feed1122Cor1.isum_ge
#print axioms LeanLab.GoldbachGaps.Feed1122Cor1.isum_le
#print axioms LeanLab.GoldbachGaps.Feed1122Cor1.leaf_rg_of_Rg_interval
