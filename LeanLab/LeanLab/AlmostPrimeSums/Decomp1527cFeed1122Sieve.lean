/-
P0002 J.-R. Chen 1973, unit U-1527 file c, burst-20261122 feed1122 split of the three sieve
estimates `Decomp1527c.SA_lower`, `Decomp1527c.sumSAq_upper`, `Decomp1527c.SB_upper`.

Each estimate is split, as in Bordignon-Johnston-Starichkova arXiv 2207.09452 Theorems 44, 50,
51 and Lemma 52, and Halberstam-Richert Chapter 11, into the linear sieve application with the
level of distribution, stated with the twin Euler product
`V_θ(N) = ∏_{2<p<N^θ, p∤N} (1 - 1/(p-1))` still in place, plus the counting inputs, and the
PROVED Mertens step `Decomp1527c.mertens_twin`, `V_θ(N) log N^θ / U_N → 1`, which turns
`V_θ(N)` into `U_N / (θ log N)` and so into the normalisation `M(N) = 2 e^γ U_N N / log² N`.

This file imports `Decomp1527c`, which defines `LevelBV`, `LevelBVTriples`, `TSet` and `Mchen`,
so the original file cannot import it back; the parents are proved here as `*_of_leaves`
theorems with exactly the parents' statements, CONDITIONAL ON `LevelBV`, respectively
`LevelBVTriples`, as the parents are.

AI-written Lean code, Claude, 2026-11-23. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.AlmostPrimeSums.Decomp1527c
import LeanLab.AlmostPrimeSums.Double243
import LeanLab.AlmostPrimeSums.Lower243

namespace LeanLab.AlmostPrimeSums.Decomp1527cFeed1122Sieve
open Finset Real Filter Topology LeanLab.ChenExplicit LeanLab.AlmostPrimeSums.Decomp1527c
attribute [local instance] Classical.propDecidable

/-! ### The proved Mertens step in two-sided form -/

/-- Two-sided eventual bounds from a limit `f(N) log N^θ / U_N → 1`. -/
theorem eventually_bounds_of_tendsto {θ : ℝ} (h0 : 0 < θ) {f : ℕ → ℝ}
    (hf : Tendsto (fun N : ℕ => f N * log ((N : ℝ) ^ θ) / U N) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 - ε) * U N / (θ * log N) ≤ f N ∧ f N ≤ (1 + ε) * U N / (θ * log N) := by
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hf ε hε
  refine ⟨max N₁ 2, fun N hN => ?_⟩
  have h := hN₁ N (le_trans (le_max_left _ _) hN)
  rw [Real.dist_eq, abs_lt] at h
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hu : 0 < U N := lt_of_lt_of_le (by norm_num) (U_ge N)
  rw [Real.log_rpow hNpos] at h
  have hL : 0 < θ * log N := mul_pos h0 hlog
  constructor
  · rw [div_le_iff₀ hL]
    have h' : 1 - ε < f N * (θ * log N) / U N := by linarith [h.1]
    have := (lt_div_iff₀ hu).mp h'
    linarith
  · rw [le_div_iff₀ hL]
    have h' : f N * (θ * log N) / U N < 1 + ε := by linarith [h.2]
    have := (div_lt_iff₀ hu).mp h'
    linarith

/-- `V_θ(N)` is eventually within a factor `1 ± ε` of `U_N / (θ log N)`; from the PROVED
`Decomp1527c.mertens_twin`. -/
theorem twinV_bounds (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 - ε) * U N / (θ * log N) ≤
        ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧ (p : ℝ) < (N : ℝ) ^ θ ∧ ¬ p ∣ N),
          (1 - 1 / ((p : ℝ) - 1)) ∧
      ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧ (p : ℝ) < (N : ℝ) ^ θ ∧ ¬ p ∣ N),
          (1 - 1 / ((p : ℝ) - 1)) ≤ (1 + ε) * U N / (θ * log N) :=
  eventually_bounds_of_tendsto h0 (mertens_twin θ h0 h1) ε hε

/-- `F(3/2) = 4 e^γ / 3`, from the closed form of `Decomp1527a.Fsieve` on `s ≤ 3`. -/
theorem Fsieve_three_halves :
    Decomp1527a.Fsieve (3 / 2) = 4 * exp eulerMascheroniConstant / 3 := by
  unfold Decomp1527a.Fsieve
  rw [if_pos (show (3 / 2 : ℝ) ≤ 3 by norm_num)]
  ring

theorem one_le_exp_gamma : 1 ≤ exp eulerMascheroniConstant :=
  Real.one_le_exp (by linarith [Real.one_half_lt_eulerMascheroniConstant])

/-! ### Leaves -/

/-- LEAF: BJS Theorem 44 and Halberstam-Richert Theorem 11.1 proof, the lower linear sieve
applied to `A = {N - p : p < N}`, before the Mertens step. Class HARD. CONDITIONAL ON
`LevelBV`: for every `η > 0` and large even `N`,
`S(A, P(N^{1/8})) ≥ (f(4) - η) (N / log N) V_{1/8}(N)`. Ingredients: `Decomp1527b.jr_lower`
with `X = π(N)`, `g(d) = 1/φ(d)`, `D = N^{1/2}/(log N)^B`, `s_N = log D / log z → 4` from
below and continuity of `f` at `4`; `card_A_dvd`, `remainder_of_levelBV`; the prime number
theorem `π(N) ~ N / log N`; the primes `p ∣ N` excluded from `A` number `O(log N)`. -/
theorem SA_sieve_lower (h : LevelBV) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (Decomp1527a.fsieve 4 - η) * ((N : ℝ) / log N) *
        ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
            (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) ∧ ¬ p ∣ N), (1 - 1 / ((p : ℝ) - 1))
      ≤ (SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) : ℝ) := by
  sorry

/-- LEAF: BJS Theorem 50, the upper linear sieve applied to each `A_q`, before the Mertens
step and before the prime sum is evaluated. Class HARD. CONDITIONAL ON `LevelBV`: for every
`η > 0` and large even `N`, `Σ_{z≤q<y, q∤N} S(A_q, P(z)) ≤ (2e^γ + η)(N / log N) V_{1/8}(N)
Σ_{N^{1/8}≤q<N^{1/3}} 1/((q - 1)(4 - 8 log q / log N))`, `z = N^{1/8}`, `y = N^{1/3}`.
Ingredients: `Decomp1527b.jr_upper` for `A_q` at level `D/q`, `X_q = π(N)/φ(q)`,
`s_q = log(D/q)/log z ∈ (4/3 - o(1), 3]` so `F(s_q) = 2e^γ/s_q`; the remainders summed over
`q` by `LevelBV` and Cauchy-Schwarz; the prime number theorem. -/
theorem sumSAq_sieve_upper (h : LevelBV) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ)
      ≤ (2 * exp eulerMascheroniConstant + η) * ((N : ℝ) / log N) *
        (∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
            (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) ∧ ¬ p ∣ N), (1 - 1 / ((p : ℝ) - 1))) *
        ∑ q ∈ (range N).filter (fun q : ℕ => q.Prime ∧ (N : ℝ) ^ ((1 : ℝ) / 8) ≤ q ∧
            (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3)),
          1 / (((q : ℝ) - 1) * (4 - 8 * log q / log N)) := by
  sorry

/-- Helper for `prime_sum_sAq_le`, BJS Theorem 50: the reciprocal prime sum over a block
`y ≤ q < x`, from the PROVED explicit Mertens second theorem `Decomp1528b.mertens2_block`,
at most `1/y + log log x - log log y + 4/log y`. -/
theorem prime_sum_block_recip {y x : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime ∧ y ≤ (q : ℝ) ∧ (q : ℝ) < x) :
    ∑ q ∈ T, (1 : ℝ) / q ≤ 1 / y + (log (log x) - log (log y)) + 4 / log y := by
  rw [← Finset.sum_filter_add_sum_filter_not T (fun q => q ≤ ⌊y⌋₊)]
  have h1 : ∑ q ∈ T.filter (fun q => q ≤ ⌊y⌋₊), (1 : ℝ) / q ≤ 1 / y := by
    have hsub : T.filter (fun q => q ≤ ⌊y⌋₊) ⊆ {⌊y⌋₊} := by
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨_, hyq, _⟩ := hT q hq.1
      have : ⌊y⌋₊ ≤ q := Nat.floor_le_of_le hyq
      rw [Finset.mem_singleton]; omega
    have hc : (T.filter (fun q => q ≤ ⌊y⌋₊)).card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    calc ∑ q ∈ T.filter (fun q => q ≤ ⌊y⌋₊), (1 : ℝ) / q
        ≤ (T.filter (fun q => q ≤ ⌊y⌋₊)).card • (1 / y) := by
          apply Finset.sum_le_card_nsmul
          intro q hq
          rw [Finset.mem_filter] at hq
          obtain ⟨_, hyq, _⟩ := hT q hq.1
          exact one_div_le_one_div_of_le (by linarith) hyq
      _ ≤ 1 • (1 / y) := by
          apply nsmul_le_nsmul_left (by positivity) hc
      _ = 1 / y := one_smul _ _
  have h2 : ∑ q ∈ T.filter (fun q => ¬ q ≤ ⌊y⌋₊), (1 : ℝ) / q ≤
      (log (log x) - log (log y)) + 4 / log y := by
    have hsub : T.filter (fun q => ¬ q ≤ ⌊y⌋₊) ⊆ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime := by
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hp, _, hqx⟩ := hT q hq.1
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, Nat.le_floor hqx.le⟩, hp⟩
    have hm := (abs_le.mp (LeanLab.AlmostPrimes.Decomp1528b.mertens2_block hy hyx)).2
    calc _ ≤ ∑ q ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ _ := by linarith
  linarith

/-- Helper for `prime_sum_sAq_le`: one step of the lower Riemann sum for
`∫ dα/(α(4-8α)) = F(b) - F(a)`, `F(α) = (log α - log(1-2α))/4`, on `1/8 ≤ a ≤ b ≤ 1/3`. -/
theorem prime_sum_step_F {a b : ℝ} (ha : 1 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 3) :
    1 / (4 - 8 * a) * (log b - log a) ≤
      (log b - log (1 - 2 * b)) / 4 - (log a - log (1 - 2 * a)) / 4 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have h1a : 0 < 1 - 2 * a := by linarith
  have h1b : 0 < 1 - 2 * b := by linarith
  have hl1 : log b - log a ≤ (b - a) / a := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have e : b / a - 1 = (b - a) / a := by field_simp
    linarith
  have hl2 : 2 * (b - a) / (1 - 2 * a) ≤ log (1 - 2 * a) - log (1 - 2 * b) := by
    have := Real.log_le_sub_one_of_pos (div_pos h1b h1a)
    rw [Real.log_div h1b.ne' h1a.ne'] at this
    have e : (1 - 2 * b) / (1 - 2 * a) - 1 = - (2 * (b - a) / (1 - 2 * a)) := by
      field_simp; ring
    linarith
  have hd0 : 0 ≤ log b - log a := by
    have := Real.log_le_log ha0 hab; linarith
  -- (log b - log a) * 2a/(1-2a) ≤ 2(b-a)/(1-2a)
  have hk : (log b - log a) * (2 * a / (1 - 2 * a)) ≤ 2 * (b - a) / (1 - 2 * a) := by
    have hc : 0 ≤ 2 * a / (1 - 2 * a) := by positivity
    calc (log b - log a) * (2 * a / (1 - 2 * a)) ≤ (b - a) / a * (2 * a / (1 - 2 * a)) :=
          mul_le_mul_of_nonneg_right hl1 hc
      _ = 2 * (b - a) / (1 - 2 * a) := by field_simp
  have e : 1 / (4 - 8 * a) * (log b - log a) =
      ((log b - log a) + (log b - log a) * (2 * a / (1 - 2 * a))) / 4 := by
    have : (4 - 8 * a) = 4 * (1 - 2 * a) := by ring
    rw [this]; field_simp; ring
  rw [e]
  linarith


/-- Helper for `prime_sum_sAq_le`: the upper Riemann sum on `K` equal steps of `[1/8, 1/3]` is at
most `(log 6)/4 + (5/12)(8h)`, `h = (5/24)/K`, by telescoping `F` and `1/(4-8α)`. -/
theorem prime_sum_riemann_upper (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ range K, 1 / (4 - 8 * (1 / 8 + ((k : ℝ) + 1) * (5 / 24 / K))) *
      (log (1 / 8 + ((k : ℝ) + 1) * (5 / 24 / K)) - log (1 / 8 + (k : ℝ) * (5 / 24 / K)))
      ≤ log 6 / 4 + 5 / 12 * (8 * (5 / 24 / K)) := by
  set h : ℝ := 5 / 24 / K with hh
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hh0 : 0 < h := by positivity
  set a : ℕ → ℝ := fun k => 1 / 8 + (k : ℝ) * h with ha
  have haK : a K = 1 / 3 := by
    simp only [ha, hh]; field_simp; ring
  have ha0 : a 0 = 1 / 8 := by simp [ha]
  have hmono : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k; simp only [ha]; push_cast; nlinarith
  have hlo : ∀ k : ℕ, 1 / 8 ≤ a k := by
    intro k; simp only [ha]; have : (0:ℝ) ≤ k := k.cast_nonneg; nlinarith
  have hhi : ∀ k ∈ range K, a (k + 1) ≤ 1 / 3 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← haK]; simp only [ha]
    have : ((k : ℝ) + 1) ≤ K := by exact_mod_cast hk
    push_cast; nlinarith
  set g : ℝ → ℝ := fun x => 1 / (4 - 8 * x) with hg
  set F : ℝ → ℝ := fun x => (log x - log (1 - 2 * x)) / 4 with hF
  have hterm : ∀ k ∈ range K, g (a (k + 1)) * (log (a (k + 1)) - log (a k)) ≤
      (F (a (k + 1)) - F (a k)) + (g (a (k + 1)) - g (a k)) * (8 * h) := by
    intro k hk
    have hb := hhi k hk
    have h1 := prime_sum_step_F (hlo k) (hmono k) hb
    have hak : 0 < a k := by linarith [hlo k]
    have hd0 : 0 ≤ log (a (k + 1)) - log (a k) := by
      have := Real.log_le_log hak (hmono k); linarith
    have hd : log (a (k + 1)) - log (a k) ≤ 8 * h := by
      have hak1 : 0 < a (k + 1) := by linarith [hlo (k+1)]
      rw [← Real.log_div hak1.ne' hak.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hak1 hak)
      have e : a (k + 1) / a k - 1 = h / a k := by
        simp only [ha]; push_cast; field_simp; ring
      have : h / a k ≤ 8 * h := by
        rw [div_le_iff₀ hak]; nlinarith [hlo k]
      linarith
    have hgm : 0 ≤ g (a (k + 1)) - g (a k) := by
      simp only [hg]
      have h4 : 0 < 4 - 8 * a (k + 1) := by linarith
      have : 4 - 8 * a (k + 1) ≤ 4 - 8 * a k := by linarith [hmono k]
      have := one_div_le_one_div_of_le h4 this
      linarith
    have e : g (a (k + 1)) * (log (a (k + 1)) - log (a k)) =
        g (a k) * (log (a (k + 1)) - log (a k)) +
          (g (a (k + 1)) - g (a k)) * (log (a (k + 1)) - log (a k)) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hd hgm
    simp only [hF, hg] at h1 ⊢
    linarith
  have hs := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_range_sub (fun k => F (a k)),
    Finset.sum_range_sub (fun k => g (a k))] at hs
  have hF1 : F (a K) - F (a 0) = log 6 / 4 := by
    rw [haK, ha0]; simp only [hF]
    have e1 : (1 : ℝ) - 2 * (1 / 3) = 1 / 3 := by norm_num
    have e2 : (1 : ℝ) - 2 * (1 / 8) = 3 / 4 := by norm_num
    rw [e1, e2]
    have : log (1 / 8 : ℝ) - log (3 / 4) = - log 6 := by
      rw [← Real.log_div (by norm_num) (by norm_num), ← Real.log_inv]; norm_num
    linarith
  have hg1 : g (a K) - g (a 0) = 5 / 12 := by
    rw [haK, ha0]; simp only [hg]; norm_num
  rw [hF1, hg1] at hs
  simpa only [ha, hg, Nat.cast_add, Nat.cast_one] using hs

set_option maxHeartbeats 1000000 in
/-- LEAF: BJS Theorem 50, evaluation of the prime sum by Mertens' second theorem and partial
summation: `Σ_{N^{1/8}≤q<N^{1/3}} 1/((q-1)(4 - 8 log q/log N)) → ∫_{1/8}^{1/3} dα/(α(4-8α))
= (log 6)/4`. Class MEDIUM. Upper half: for every `η > 0`, eventually the sum is at most
`(log 6)/4 + η`. -/
theorem prime_sum_sAq_le :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ q ∈ (range N).filter (fun q : ℕ => q.Prime ∧ (N : ℝ) ^ ((1 : ℝ) / 8) ≤ q ∧
            (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3)),
          1 / (((q : ℝ) - 1) * (4 - 8 * log q / log N)) ≤ log 6 / 4 + η := by
  intro η hη
  set e : ℝ := min η 1 with he
  have he0 : 0 < e := lt_min hη one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heη : e ≤ η := min_le_left _ _
  set K : ℕ := ⌈25 / (9 * e)⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKe : 5 / 12 * (8 * (5 / 24 / (K : ℝ))) ≤ e / 4 := by
    have h1 : 25 / (9 * e) ≤ (K : ℝ) := by
      have := Nat.le_ceil (25 / (9 * e))
      have : ((⌈25 / (9 * e)⌉₊ : ℕ) : ℝ) ≤ K := by exact_mod_cast (by omega : ⌈25 / (9 * e)⌉₊ ≤ K)
      linarith
    rw [div_le_iff₀ (by positivity)] at h1
    have e2 : 5 / 12 * (8 * (5 / 24 / (K : ℝ))) = 25 / 36 / K := by field_simp; ring
    rw [e2, div_le_iff₀ (by positivity)]
    nlinarith
  set M1 : ℝ := max 2 (8 * K / e) with hM1
  have hM1_2 : 2 ≤ M1 := le_max_left _ _
  have hM1_K : 8 * K / e ≤ M1 := le_max_right _ _
  have hM1_e : 8 / e ≤ M1 := by
    refine le_trans ?_ hM1_K
    exact div_le_div_of_nonneg_right (by nlinarith) he0.le
  have hev : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ max (8 * log M1) (256 * K / e) ≤ log (N : ℝ) := by
    have h1 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
    have h2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max (8 * log M1) (256 * K / e))
    exact h1.and h2
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hN2, hL⟩ := hN₀ N hN
  set L : ℝ := log (N : ℝ) with hLdef
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hL1 : 8 * log M1 ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : 256 * K / e ≤ L := le_trans (le_max_right _ _) hL
  set y0 : ℝ := exp (L / 8) with hy0
  have hy0M : M1 ≤ y0 := by
    rw [hy0, ← Real.exp_log (by linarith : (0:ℝ) < M1)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hy02 : 2 ≤ y0 := le_trans hM1_2 hy0M
  have hy0pos : 0 < y0 := by linarith
  set ε0 : ℝ := 2 / y0 with hε0
  have hε0e : ε0 ≤ e / 4 := by
    rw [hε0, div_le_iff₀ hy0pos]
    have : 8 / e ≤ y0 := le_trans hM1_e hy0M
    rw [div_le_iff₀ he0] at this; nlinarith
  have hε00 : 0 ≤ ε0 := by positivity
  set E : ℝ := 1 / y0 + 32 / L with hE
  have hKE : (K : ℝ) * E ≤ e / 4 := by
    have a1 : (K : ℝ) * (1 / y0) ≤ e / 8 := by
      have : 8 * K / e ≤ y0 := le_trans hM1_K hy0M
      rw [div_le_iff₀ he0] at this
      rw [mul_one_div, div_le_iff₀ hy0pos]; nlinarith
    have a2 : (K : ℝ) * (32 / L) ≤ e / 8 := by
      rw [div_le_iff₀ he0] at hL2
      rw [mul_div_assoc', div_le_iff₀ hLpos]; nlinarith
    rw [hE, mul_add]; linarith
  have hE0 : 0 ≤ E := by positivity
  set h : ℝ := 5 / 24 / K with hh
  have hh0 : 0 < h := by positivity
  set a : ℕ → ℝ := fun k => 1 / 8 + (k : ℝ) * h with ha
  set S := (range N).filter (fun q : ℕ => q.Prime ∧ (N : ℝ) ^ ((1 : ℝ) / 8) ≤ q ∧
            (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3)) with hS
  have hmemS : ∀ q ∈ S, q.Prime ∧ 1 / 8 ≤ log q / L ∧ log q / L < 1 / 3 := by
    intro q hq
    rw [hS, Finset.mem_filter] at hq
    obtain ⟨_, hp, hlo, hhi⟩ := hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
    rw [Real.rpow_def_of_pos hN0] at hlo hhi
    refine ⟨hp, ?_, ?_⟩
    · rw [le_div_iff₀ hLpos]
      have := Real.log_le_log (Real.exp_pos _) hlo
      rw [Real.log_exp] at this; linarith
    · rw [div_lt_iff₀ hLpos]
      have := Real.log_lt_log hq0 hhi
      rw [Real.log_exp] at this; linarith
  set φ : ℕ → ℕ := fun q => ⌊(log q / L - 1 / 8) / h⌋₊ with hφ
  have hmaps : ∀ q ∈ S, φ q ∈ range K := by
    intro q hq
    obtain ⟨_, h1, h2⟩ := hmemS q hq
    rw [Finset.mem_range, hφ]
    apply (Nat.floor_lt (div_nonneg (by linarith) hh0.le)).mpr
    rw [div_lt_iff₀ hh0, hh]
    have : (K : ℝ) * (5 / 24 / K) = 5 / 24 := by field_simp
    rw [this]; linarith
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- fiber bound
  have hfib : ∀ k ∈ range K, ∑ q ∈ S.filter (fun q => φ q = k),
      1 / (((q : ℝ) - 1) * (4 - 8 * log q / L)) ≤
      (1 + ε0) * (1 / (4 - 8 * a (k + 1)) * (log (a (k + 1)) - log (a k)) + E) := by
    intro k hk
    have hkK : ((k : ℝ) + 1) ≤ K := by exact_mod_cast (Finset.mem_range.mp hk)
    have hak_lo : 1 / 8 ≤ a k := by
      simp only [ha]; have : (0:ℝ) ≤ k := k.cast_nonneg; nlinarith
    have hak1_hi : a (k + 1) ≤ 1 / 3 := by
      simp only [ha, hh]; push_cast
      have : ((k : ℝ) + 1) * (5 / 24 / K) ≤ 5 / 24 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have hmono : a k ≤ a (k + 1) := by simp only [ha]; push_cast; nlinarith
    have hak0 : 0 < a k := by linarith
    have hD0 : 0 < 4 - 8 * a (k + 1) := by linarith
    have hin : ∀ q ∈ S.filter (fun q => φ q = k),
        q.Prime ∧ a k * L ≤ log q ∧ log q < a (k + 1) * L := by
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hp, h1, h2⟩ := hmemS q hq.1
      have hφk := hq.2
      have ht0 : 0 ≤ (log q / L - 1 / 8) / h := div_nonneg (by linarith) hh0.le
      refine ⟨hp, ?_, ?_⟩
      · have := Nat.floor_le ht0
        rw [show (⌊(log q / L - 1 / 8) / h⌋₊ : ℝ) = k by rw [← hφk]] at this
        rw [le_div_iff₀ hh0] at this
        have : a k ≤ log q / L := by simp only [ha]; linarith
        rwa [le_div_iff₀ hLpos] at this
      · have := Nat.lt_floor_add_one ((log q / L - 1 / 8) / h)
        rw [show (⌊(log q / L - 1 / 8) / h⌋₊ : ℝ) = k by rw [← hφk]] at this
        rw [div_lt_iff₀ hh0] at this
        have : log q / L < a (k + 1) := by simp only [ha]; push_cast; linarith
        rwa [div_lt_iff₀ hLpos] at this
    set y : ℝ := exp (a k * L) with hy
    set x : ℝ := exp (a (k + 1) * L) with hx
    have hyy0 : y0 ≤ y := by
      have := mul_le_mul_of_nonneg_right hak_lo hLpos.le
      rw [hy, hy0]; exact Real.exp_le_exp.mpr (by linarith)
    have hy2 : 2 ≤ y := le_trans hy02 hyy0
    have hyx : y ≤ x := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hmono hLpos.le)
    have hT : ∀ q ∈ S.filter (fun q => φ q = k), q.Prime ∧ y ≤ (q : ℝ) ∧ (q : ℝ) < x := by
      intro q hq
      obtain ⟨hp, h1, h2⟩ := hin q hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
      refine ⟨hp, ?_, ?_⟩
      · rw [hy, ← Real.exp_log hq0]; exact Real.exp_le_exp.mpr h1
      · rw [hx, ← Real.exp_log hq0]; exact Real.exp_lt_exp.mpr h2
    have hrec := prime_sum_block_recip hy2 hyx _ hT
    have hlogs : log (log x) - log (log y) = log (a (k + 1)) - log (a k) := by
      rw [hx, hy, Real.log_exp, Real.log_exp, Real.log_mul (by linarith : (0:ℝ) < a (k + 1)).ne' hLpos.ne',
        Real.log_mul hak0.ne' hLpos.ne']; ring
    have hly : 4 / log y ≤ 32 / L := by
      have := mul_le_mul_of_nonneg_right hak_lo hLpos.le
      rw [hy, Real.log_exp, div_le_div_iff₀ (by positivity) hLpos]; nlinarith
    have hy1 : 1 / y ≤ 1 / y0 := one_div_le_one_div_of_le hy0pos hyy0
    rw [hlogs] at hrec
    set g : ℝ := 1 / (4 - 8 * a (k + 1)) with hg
    have hg0 : 0 ≤ g := by positivity
    have hg1 : g ≤ 1 := by
      rw [hg, div_le_one hD0]; linarith
    have hpt : ∀ q ∈ S.filter (fun q => φ q = k),
        1 / (((q : ℝ) - 1) * (4 - 8 * log q / L)) ≤ (1 + ε0) * g * (1 / (q : ℝ)) := by
      intro q hq
      obtain ⟨hp, h1, h2⟩ := hin q hq
      obtain ⟨_, hyq, _⟩ := hT q hq
      have hq2 : (2 : ℝ) ≤ q := le_trans hy2 hyq
      have hq1 : 0 < (q : ℝ) - 1 := by linarith
      have hDD : 4 - 8 * a (k + 1) ≤ 4 - 8 * log q / L := by
        have : log q / L < a (k + 1) := by rw [div_lt_iff₀ hLpos]; linarith
        have e3 : 8 * log q / L = 8 * (log q / L) := by ring
        rw [e3]; linarith
      calc 1 / (((q : ℝ) - 1) * (4 - 8 * log q / L))
          ≤ 1 / (((q : ℝ) - 1) * (4 - 8 * a (k + 1))) :=
            one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hDD hq1.le)
        _ = g * (1 / ((q : ℝ) - 1)) := by rw [hg]; field_simp
        _ ≤ g * ((1 + ε0) * (1 / (q : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ hg0
            have hq0 : (0:ℝ) < q := by linarith
            rw [mul_one_div, div_le_div_iff₀ hq1 hq0]
            have : 1 ≤ ε0 * ((q : ℝ) - 1) := by
              rw [hε0, div_mul_eq_mul_div, le_div_iff₀ hy0pos]; linarith
            nlinarith
        _ = (1 + ε0) * g * (1 / (q : ℝ)) := by ring
    calc _ ≤ ∑ q ∈ S.filter (fun q => φ q = k), (1 + ε0) * g * (1 / (q : ℝ)) :=
          Finset.sum_le_sum hpt
      _ = (1 + ε0) * g * ∑ q ∈ S.filter (fun q => φ q = k), (1 : ℝ) / q := by
          rw [Finset.mul_sum]
      _ ≤ (1 + ε0) * g * (1 / y + (log (a (k + 1)) - log (a k)) + 4 / log y) :=
          mul_le_mul_of_nonneg_left hrec (by positivity)
      _ ≤ (1 + ε0) * (g * (log (a (k + 1)) - log (a k)) + E) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hE' : 1 / y + 4 / log y ≤ E := by rw [hE]; linarith
          have : g * (1 / y + 4 / log y) ≤ E := by
            have hnn : 0 ≤ 1 / y + 4 / log y := by
              have : 0 < log y := by rw [hy, Real.log_exp]; positivity
              positivity
            nlinarith
          nlinarith
  calc _ ≤ ∑ k ∈ range K,
        (1 + ε0) * (1 / (4 - 8 * a (k + 1)) * (log (a (k + 1)) - log (a k)) + E) :=
        Finset.sum_le_sum hfib
    _ = (1 + ε0) * (∑ k ∈ range K, 1 / (4 - 8 * a (k + 1)) * (log (a (k + 1)) - log (a k))
          + K * E) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
    _ ≤ (1 + ε0) * (log 6 / 4 + e / 4 + e / 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hR := prime_sum_riemann_upper K hK1
        simp only [ha, hh, Nat.cast_add, Nat.cast_one] at hR ⊢
        linarith
    _ ≤ log 6 / 4 + η := by
        have hl6 : log 6 < 2 := by
          rw [Real.log_lt_iff_lt_exp (by norm_num)]
          have := Real.exp_one_gt_d9
          have h2 : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
          rw [h2]; nlinarith
        have hl60 : 0 < log 6 := Real.log_pos (by norm_num)
        nlinarith

/-- LEAF: BJS Theorem 51, the upper linear sieve applied to `B = {N - m : m ∈ T}`, before the
Mertens step and before `|T|` is evaluated; Chen's switching principle. Class HARD.
CONDITIONAL ON `LevelBVTriples`: for every `η > 0` and large even `N`,
`S(B, P(N^{1/3})) ≤ (F(3/2) + η) |T| V_{1/3}(N)`. Ingredients: `Decomp1527b.jr_upper` with
`X = |T|`, `g(d) = 1/φ(d)`, `D = N^{1/2}/(log N)^B`, `s = log D / log y → 3/2`, continuity of
`F`; `card_bset_dvd`, `siftedBy_iff_of_mem_bset`, `sum_TSet_coprime_loss_le`,
`remainder_bset_full_mass_of_levelBVTriples`. -/
theorem SB_sieve_upper (h : LevelBVTriples) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ)
      ≤ (Decomp1527a.Fsieve (3 / 2) + η) *
        (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ) *
        ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
            (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3) ∧ ¬ p ∣ N), (1 - 1 / ((p : ℝ) - 1)) := by
  sorry

/-- LEAF: BJS Lemma 52, the size of Chen's switched sequence: `|T| ≤ (c̄ + η) N / log N`
eventually, where `c̄ = ∫_{1/8}^{1/3} log(2-3β)/(β(1-β)) dβ`, from the prime number theorem for
`π(N/(p₁p₂))` and Mertens' theorem, the inner integral being
`∫_{1/3}^{(1-α)/2} dβ/(β(1-α-β)) = log(2-3α)/(1-α)`. Class HARD. -/
theorem card_TSet_le :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ)
      ≤ ((∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) + η) * (N / log N) := by
  exact Double243.triple_mass_upper

/-- Coefficient algebra for `sumSAq_upper_of_leaves`. -/
theorem coef_sumSAq {E δ L η : ℝ} (hE1 : 1 ≤ E) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 40)
    (hδη : δ ≤ η / 40) (hL0 : 0 < L) (hL1 : L ≤ 1 / 2) (hη : 0 < η) :
    8 * (2 * E + δ) * (1 + δ) * (L + δ) / 2 ≤ (4 * L + η) * (2 * E) := by
  have hA : (1 + δ) * (L + δ) ≤ L + 2 * δ := by
    nlinarith [mul_le_mul_of_nonneg_left hL1 hδ0.le, mul_le_mul_of_nonneg_left hδ1 hδ0.le]
  have hB : (2 * E + δ) * ((1 + δ) * (L + δ)) ≤ (2 * E + δ) * (L + 2 * δ) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have hC : (2 * E + δ) * (L + 2 * δ) ≤ 2 * E * L + 5 * E * δ := by
    nlinarith [mul_le_mul_of_nonneg_left hL1 hδ0.le, mul_le_mul_of_nonneg_left hδ1 hδ0.le,
      mul_le_mul_of_nonneg_left hE1 hδ0.le]
  have hD : δ * E ≤ η / 40 * E := mul_le_mul_of_nonneg_right hδη (by linarith)
  have hEη : 0 ≤ η * E := by positivity
  have hX : 8 * (2 * E + δ) * (1 + δ) * (L + δ) / 2 = 4 * ((2 * E + δ) * ((1 + δ) * (L + δ))) := by
    ring
  rw [hX]
  nlinarith [hB, hC, hD, hEη]

/-- Coefficient algebra for `SB_upper_of_leaves`. -/
theorem coef_SB {E δ c η : ℝ} (hE1 : 1 ≤ E) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 40)
    (hδη : δ ≤ η / 40) (hcδ : 0 ≤ c + δ) (hc1 : c < 0.3631) (hη : 0 < η) :
    3 * (4 * E / 3 + δ) * (c + δ) * (1 + δ) / 2 ≤ (c + η) * (2 * E) := by
  have hY : (4 * E / 3 + δ) * (1 + δ) ≤ 4 * E / 3 + 3 * E * δ := by
    nlinarith [mul_le_mul_of_nonneg_left hE1 hδ0.le, mul_le_mul_of_nonneg_left hδ1 hδ0.le]
  have hZ := mul_le_mul_of_nonneg_right hY hcδ
  have hW2 : E * δ * (c + δ) ≤ E * δ * (2 / 5) :=
    mul_le_mul_of_nonneg_left (by norm_num at hc1; linarith) (by positivity)
  have hD : δ * E ≤ η / 40 * E := mul_le_mul_of_nonneg_right hδη (by linarith)
  have hEη : 0 ≤ η * E := by positivity
  have hX : 3 * (4 * E / 3 + δ) * (c + δ) * (1 + δ) / 2 =
      3 / 2 * ((4 * E / 3 + δ) * (1 + δ) * (c + δ)) := by ring
  rw [hX]
  nlinarith [hZ, hW2, hD, hEη]

/-! ### Assemblies -/

/-- **Parent `Decomp1527c.SA_lower`, assembled from the leaf** `SA_sieve_lower` and the PROVED
`mertens_twin`, `fsieve_four`. Same statement as the parent, CONDITIONAL ON `LevelBV`. -/
theorem SA_lower_of_leaves (h : LevelBV) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (2 * log 3 - η) * Mchen N ≤ SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) := by
  intro η hη
  set δ : ℝ := min (1 / 40) (η / 40) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 40 := min_le_left _ _
  have hδη : δ ≤ η / 40 := min_le_right _ _
  obtain ⟨N₁, hS⟩ := SA_sieve_lower h δ hδ0
  obtain ⟨N₂, hV⟩ := twinV_bounds (1 / 8) (by norm_num) (by norm_num) δ hδ0
  refine ⟨max (max N₁ N₂) 2, fun N he hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hu : 0 < U N := lt_of_lt_of_le (by norm_num) (U_ge N)
  have hs := hS N he hN1
  have hv := (hV N hN2).1
  set V := ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
            (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) ∧ ¬ p ∣ N), (1 - 1 / ((p : ℝ) - 1))
  set E := exp eulerMascheroniConstant with hE
  have hE1 : 1 ≤ E := one_le_exp_gamma
  have hl3 : 1 < log (3 : ℝ) := by
    have := Real.log_two_gt_d9; have := Real.log_three_gt_d9; norm_num at *; linarith
  have hl3' : log (3 : ℝ) < 2 := by
    have := Real.log_three_lt_d9; norm_num at *; linarith
  have hf4 : Decomp1527a.fsieve 4 = E * log 3 / 2 := Decomp1527a.fsieve_four
  have hcoef : 0 ≤ (Decomp1527a.fsieve 4 - δ) * ((N : ℝ) / log N) := by
    apply mul_nonneg _ (div_nonneg hNpos.le hlog.le)
    rw [hf4]; nlinarith
  have h1 := mul_le_mul_of_nonneg_left hv hcoef
  set W : ℝ := U N * N / log N ^ 2 with hW
  have hWpos : 0 < W := by positivity
  have hrhs : (Decomp1527a.fsieve 4 - δ) * ((N : ℝ) / log N) *
      ((1 - δ) * U N / (1 / 8 * log N)) = 8 * (Decomp1527a.fsieve 4 - δ) * (1 - δ) * W := by
    rw [hW]; field_simp
  have hM : Mchen N = 2 * E * W := by
    unfold Mchen; rw [hW]; try ring
  have hc : (2 * log 3 - η) * (2 * E) ≤ 8 * (Decomp1527a.fsieve 4 - δ) * (1 - δ) := by
    rw [hf4]; nlinarith [mul_le_mul_of_nonneg_left hE1 hδ0.le, mul_le_mul_of_nonneg_left hδη (by linarith : (0:ℝ) ≤ E)]
  rw [hM]
  calc (2 * log 3 - η) * (2 * E * W) = ((2 * log 3 - η) * (2 * E)) * W := by ring
    _ ≤ (8 * (Decomp1527a.fsieve 4 - δ) * (1 - δ)) * W := mul_le_mul_of_nonneg_right hc hWpos.le
    _ = _ := hrhs.symm
    _ ≤ _ := h1
    _ ≤ _ := hs

/-- **Parent `Decomp1527c.sumSAq_upper`, assembled from the leaves** `sumSAq_sieve_upper`,
`prime_sum_sAq_le` and the PROVED `mertens_twin`. Same statement as the parent, CONDITIONAL ON
`LevelBV`. -/
theorem sumSAq_upper_of_leaves (h : LevelBV) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ (log 6 + η) * Mchen N := by
  intro η hη
  set δ : ℝ := min (1 / 40) (η / 40) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 40 := min_le_left _ _
  have hδη : δ ≤ η / 40 := min_le_right _ _
  obtain ⟨N₁, hS⟩ := sumSAq_sieve_upper h δ hδ0
  obtain ⟨N₂, hV⟩ := twinV_bounds (1 / 8) (by norm_num) (by norm_num) δ hδ0
  obtain ⟨N₃, hQ⟩ := prime_sum_sAq_le δ hδ0
  refine ⟨max (max N₁ N₂) (max N₃ 2), fun N he hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN4 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hu : 0 < U N := lt_of_lt_of_le (by norm_num) (U_ge N)
  have hs := hS N he hN1
  have hv := hV N hN2
  have hq := hQ N hN3
  set V := ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
            (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) ∧ ¬ p ∣ N), (1 - 1 / ((p : ℝ) - 1))
  set Q := ∑ q ∈ (range N).filter (fun q : ℕ => q.Prime ∧ (N : ℝ) ^ ((1 : ℝ) / 8) ≤ q ∧
            (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3)),
          1 / (((q : ℝ) - 1) * (4 - 8 * log q / log N))
  set E := exp eulerMascheroniConstant with hE
  have hE1 : 1 ≤ E := one_le_exp_gamma
  set S := (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ)
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hVpos : 0 < V := lt_of_lt_of_le (by
    apply div_pos (mul_pos (by linarith) hu) (mul_pos (by norm_num) hlog)) hv.1
  have hcpos : 0 < (2 * E + δ) * ((N : ℝ) / log N) * V := by positivity
  have hQ0 : 0 ≤ Q := by
    by_contra hneg
    push Not at hneg
    have : (2 * E + δ) * ((N : ℝ) / log N) * V * Q < 0 := mul_neg_of_pos_of_neg hcpos hneg
    linarith
  have hl6 : log (6 : ℝ) < 2 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have := Real.log_two_lt_d9; have := Real.log_three_lt_d9; norm_num at *; linarith
  have hl6' : 0 < log (6 : ℝ) := log_pos (by norm_num)
  set L := log (6 : ℝ) / 4 with hL
  have hL0 : 0 < L := by positivity
  have hL1 : L ≤ 1 / 2 := by rw [hL]; linarith
  have h1 : S ≤ (2 * E + δ) * ((N : ℝ) / log N) * V * (L + δ) :=
    hs.trans (mul_le_mul_of_nonneg_left hq hcpos.le)
  have hc2 : 0 ≤ (2 * E + δ) * ((N : ℝ) / log N) * (L + δ) := by positivity
  have h2 : (2 * E + δ) * ((N : ℝ) / log N) * V * (L + δ) ≤
      (2 * E + δ) * ((N : ℝ) / log N) * ((1 + δ) * U N / (1 / 8 * log N)) * (L + δ) := by
    have := mul_le_mul_of_nonneg_left hv.2 hc2
    nlinarith [this]
  set W : ℝ := U N * N / log N ^ 2 with hW
  have hWpos : 0 < W := by positivity
  have hrhs : (2 * E + δ) * ((N : ℝ) / log N) * ((1 + δ) * U N / (1 / 8 * log N)) * (L + δ)
      = 8 * (2 * E + δ) * (1 + δ) * (L + δ) * W := by
    rw [hW]; field_simp
  have hM : Mchen N = 2 * E * W := by
    unfold Mchen; rw [hW]; try ring
  have hc : 8 * (2 * E + δ) * (1 + δ) * (L + δ) / 2 ≤ (log 6 + η) * (2 * E) := by
    have h6 : log (6 : ℝ) = 4 * L := by rw [hL]; ring
    rw [h6]
    exact coef_sumSAq hE1 hδ0 hδ1 hδη hL0 hL1 hη
  rw [hM]
  calc S / 2 ≤ (8 * (2 * E + δ) * (1 + δ) * (L + δ) * W) / 2 := by
        rw [← hrhs]; linarith
    _ = (8 * (2 * E + δ) * (1 + δ) * (L + δ) / 2) * W := by ring
    _ ≤ ((log 6 + η) * (2 * E)) * W := mul_le_mul_of_nonneg_right hc hWpos.le
    _ = (log 6 + η) * (2 * E * W) := by ring

/-- **Parent `Decomp1527c.SB_upper`, assembled from the leaves** `SB_sieve_upper`,
`card_TSet_le` and the PROVED `mertens_twin`, `cbar_lt'`. Same statement as the parent,
CONDITIONAL ON `LevelBVTriples`. -/
theorem SB_upper_of_leaves (h : LevelBVTriples) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ ((∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) + η) * Mchen N := by
  intro η hη
  set δ : ℝ := min (1 / 40) (η / 40) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 40 := min_le_left _ _
  have hδη : δ ≤ η / 40 := min_le_right _ _
  obtain ⟨N₁, hS⟩ := SB_sieve_upper h δ hδ0
  obtain ⟨N₂, hV⟩ := twinV_bounds (1 / 3) (by norm_num) (by norm_num) δ hδ0
  obtain ⟨N₃, hT⟩ := card_TSet_le δ hδ0
  refine ⟨max (max N₁ N₂) (max N₃ 2), fun N he hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN4 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hu : 0 < U N := lt_of_lt_of_le (by norm_num) (U_ge N)
  have hs := hS N he hN1
  have hv := hV N hN2
  have ht := hT N hN3
  rw [Fsieve_three_halves] at hs
  set V := ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
            (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3) ∧ ¬ p ∣ N), (1 - 1 / ((p : ℝ) - 1))
  set T := (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ)
  set c := ∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))
  set E := exp eulerMascheroniConstant with hE
  have hE1 : 1 ≤ E := one_le_exp_gamma
  have hc1 : c < 0.3631 := cbar_lt'
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  have hVpos : 0 < V := lt_of_lt_of_le (by
    apply div_pos (mul_pos (by linarith) hu) (mul_pos (by norm_num) hlog)) hv.1
  have hNl : 0 < (N : ℝ) / log N := div_pos hNpos hlog
  have hcδ : 0 ≤ c + δ := by
    by_contra hneg; push Not at hneg
    have : (c + δ) * ((N : ℝ) / log N) < 0 := mul_neg_of_neg_of_pos hneg hNl
    linarith
  have hF : 0 ≤ 4 * E / 3 + δ := by positivity
  have h1 : (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) ≤
      (4 * E / 3 + δ) * ((c + δ) * ((N : ℝ) / log N)) * V :=
    hs.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hF) hVpos.le)
  have hc2 : 0 ≤ (4 * E / 3 + δ) * ((c + δ) * ((N : ℝ) / log N)) := by positivity
  have h2 := mul_le_mul_of_nonneg_left hv.2 hc2
  set W : ℝ := U N * N / log N ^ 2 with hW
  have hWpos : 0 < W := by positivity
  have hrhs : (4 * E / 3 + δ) * ((c + δ) * ((N : ℝ) / log N)) * ((1 + δ) * U N / (1 / 3 * log N))
      = 3 * (4 * E / 3 + δ) * (c + δ) * (1 + δ) * W := by
    rw [hW]; field_simp
  have hM : Mchen N = 2 * E * W := by
    unfold Mchen; rw [hW]; try ring
  have hc : 3 * (4 * E / 3 + δ) * (c + δ) * (1 + δ) / 2 ≤ (c + η) * (2 * E) :=
    coef_SB hE1 hδ0 hδ1 hδη hcδ hc1 hη
  rw [hM]
  calc (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ (3 * (4 * E / 3 + δ) * (c + δ) * (1 + δ) * W) / 2 := by
        rw [← hrhs]; linarith
    _ = (3 * (4 * E / 3 + δ) * (c + δ) * (1 + δ) / 2) * W := by ring
    _ ≤ ((c + η) * (2 * E)) * W := mul_le_mul_of_nonneg_right hc hWpos.le
    _ = (c + η) * (2 * E * W) := by ring


/-- The middle prime sum converges to the scaled kernel integral.
Derived from BJS p. 54 equation 173 and the two proved Abel bounds. -/
theorem prime_sum_sAq_tendsto :
    Tendsto (fun N : ℕ =>
      ∑ q ∈ (range N).filter (fun q : ℕ => q.Prime ∧ (N : ℝ) ^ ((1 : ℝ) / 8) ≤ q ∧
          (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3)),
        1 / (((q : ℝ) - 1) * (4 - 8 * log q / log N))) atTop (𝓝 (log 6 / 4)) := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzlim : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 8)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp tendsto_natCast_atTop_atTop
  have hlow : ∀ᶠ N : ℕ in atTop,
      log 6 / 4 - 72 / log N ≤
      ∑ q ∈ (range N).filter (fun q : ℕ => q.Prime ∧ (N : ℝ) ^ ((1 : ℝ) / 8) ≤ q ∧
          (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3)),
        1 / (((q : ℝ) - 1) * (4 - 8 * log q / log N)) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hzlim.eventually_ge_atTop 2] with N hN hz2
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
    let z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8)
    let y : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3)
    have hzlog : log z = log N / 8 := by dsimp [z]; rw [log_rpow hNp]; ring
    have hylog : log y = log N / 3 := by dsimp [y]; rw [log_rpow hNp]; ring
    have hzy : z ≤ y := rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
    have hset : (range N).filter (fun q : ℕ => q.Prime ∧
        (N : ℝ) ^ ((1 : ℝ) / 8) ≤ q ∧ (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3)) =
        LeanLab.ChenExplicit.D1552.primesIco z y := by
      ext q
      simp only [mem_filter, mem_range, LeanLab.ChenExplicit.D1552.primesIco, Nat.lt_ceil]
      have hyN : y ≤ (N : ℝ) := rpow_le_self_of_one_le
        (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
      constructor
      · rintro ⟨hqN, hprime, hlow, hhigh⟩
        exact ⟨hhigh, hprime, hlow⟩
      · rintro ⟨hhigh, hprime, hlow⟩
        exact ⟨by exact_mod_cast hhigh.trans_le hyN, hprime, hlow, hhigh⟩
    have hk := Lower243.logarithmic_kernel_lower z y (log N / 2) hz2 hzy
      (by rw [hylog]; linarith)
    have hi : ((log (log y) - log (log N / 2 - log y)) -
        (log (log z) - log (log N / 2 - log z))) = log 6 := by
      rw [hzlog, hylog,
        show log (N : ℝ) / 2 - log N / 3 = log N / 6 by ring,
        show log (N : ℝ) / 2 - log N / 8 = (3 / 8) * log N by ring,
        log_div hl.ne' (by norm_num), log_div hl.ne' (by norm_num),
        log_div hl.ne' (by norm_num), log_mul (by norm_num : (3 / 8 : ℝ) ≠ 0) hl.ne',
        log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)]
      ring
    rw [hi, hzlog, hylog] at hk
    have hpoint : (log (N : ℝ) / 8) *
        (∑ q ∈ LeanLab.ChenExplicit.D1552.primesIco z y,
          1 / ((q : ℝ) * (log N / 2 - log q))) ≤
        ∑ q ∈ LeanLab.ChenExplicit.D1552.primesIco z y,
          1 / (((q : ℝ) - 1) * (4 - 8 * log q / log N)) := by
      rw [mul_sum]
      apply sum_le_sum
      intro q hq
      obtain ⟨hqmem, hprime, _⟩ := mem_filter.mp hq
      have hqy : (q : ℝ) < y := Nat.lt_ceil.mp (mem_range.mp hqmem)
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hprime.pos
      have hq1 : 0 < (q : ℝ) - 1 := by
        have hh : (1 : ℝ) < q := by exact_mod_cast hprime.one_lt
        linarith
      have hden : 0 < log (N : ℝ) / 2 - log q := by
        have hh := log_lt_log hq0 hqy
        rw [hylog] at hh
        linarith
      have hscale : 4 - 8 * log q / log (N : ℝ) =
          8 / log N * (log N / 2 - log q) := by field_simp [hl.ne']; ring
      have heq : 1 / (((q : ℝ) - 1) * (4 - 8 * log q / log N)) =
          log N / 8 * (1 / (((q : ℝ) - 1) * (log N / 2 - log q))) := by
        rw [hscale]
        field_simp [hl.ne', hq1.ne', hden.ne']
      rw [heq]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact one_div_le_one_div_of_le (mul_pos hq1 hden)
        (mul_le_mul_of_nonneg_right (by linarith : (q : ℝ) - 1 ≤ q) hden.le)
    rw [hset]
    calc
      log 6 / 4 - 72 / log (N : ℝ) = log N / 8 *
        (log 6 / (log N / 2) - 12 / (log N / 8 * (log N / 2 - log N / 3))) := by
          field_simp [hl.ne']
          <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ _ := hpoint
  have hlowlim : Tendsto (fun N : ℕ => log 6 / 4 - 72 / log N) atTop (𝓝 (log 6 / 4)) := by
    simpa using (tendsto_const_nhds.sub (hlog.const_div_atTop (72 : ℝ)))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := prime_sum_sAq_le (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (hlow.and (hlowlim.eventually (lt_mem_nhds (by linarith : log (6 : ℝ) / 4 - ε < log 6 / 4))))
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hu := hN₁ N ((le_max_left _ _).trans hN)
  obtain ⟨hlo, hclose⟩ := hN₂ N ((le_max_right _ _).trans hN)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end LeanLab.AlmostPrimeSums.Decomp1527cFeed1122Sieve
