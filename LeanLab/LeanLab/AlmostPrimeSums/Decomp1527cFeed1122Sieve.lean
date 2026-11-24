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

/-- LEAF: BJS Theorem 50, evaluation of the prime sum by Mertens' second theorem and partial
summation: `Σ_{N^{1/8}≤q<N^{1/3}} 1/((q-1)(4 - 8 log q/log N)) → ∫_{1/8}^{1/3} dα/(α(4-8α))
= (log 6)/4`. Class MEDIUM. Upper half: for every `η > 0`, eventually the sum is at most
`(log 6)/4 + η`. -/
theorem prime_sum_sAq_le :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ q ∈ (range N).filter (fun q : ℕ => q.Prime ∧ (N : ℝ) ^ ((1 : ℝ) / 8) ≤ q ∧
            (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3)),
          1 / (((q : ℝ) - 1) * (4 - 8 * log q / log N)) ≤ log 6 / 4 + η := by
  sorry

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
  sorry

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

end LeanLab.AlmostPrimeSums.Decomp1527cFeed1122Sieve
