import Mathlib
import LeanLab.GoldbachGaps.Goldston1990Main
import LeanLab.GoldbachGaps.Goldston1990Sec5

namespace LeanLab.GoldbachGaps.DecompJ205
open Real Chebyshev Finset Filter Topology
open LeanLab.GoldbachGaps.Goldston1990

lemma fejer_eq (N K : ℕ) (hNK : K ≤ N) :
    fejer N K = ∑ n ∈ Icc (N - K) (N + K), ((K : ℝ) - |(n : ℝ) - N|) * Rg n := by
  unfold fejer
  apply sum_bij (fun j _ => j + N - K)
  case hi =>
    intro a ha
    simp only [mem_range] at ha
    simp only [mem_Icc]
    have h1 : N - K ≤ a + N - K := by omega
    have h2 : a + N - K ≤ N + K := by omega
    exact ⟨h1, h2⟩
  case h =>
    intro a ha
    simp only [mem_range] at ha
    congr 2
    · have h1 : ((a + N - K : ℕ) : ℝ) = (a : ℝ) + (N : ℝ) - (K : ℝ) := by
        have : a + N ≥ K := by omega
        rw [Nat.cast_sub this, Nat.cast_add]
      rw [h1]
      have : (a : ℝ) + (N : ℝ) - (K : ℝ) - (N : ℝ) = (a : ℝ) - (K : ℝ) := by ring
      rw [this]
    · have h1 : N + a - K = a + N - K := by omega
      rw [h1]
  case i_inj =>
    intro a1 ha1 a2 ha2 heq
    omega
  case i_surj =>
    intro b hb
    simp only [mem_Icc] at hb
    use b - (N - K)
    have h1 : N - K ≤ b := hb.1
    have h2 : b ≤ N + K := hb.2
    refine ⟨?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega

/-- `Σ_{|n| ≤ K} R(N + n)` in both spellings, for `K ≤ N`. -/
lemma Rsum_eq_Icc (N K : ℕ) (hKN : K ≤ N) :
    ∑ n ∈ Icc (N - K) (N + K), Rg n = Rsum N K := by
  symm
  unfold Rsum
  apply sum_bij (fun j _ => j + N - K)
  case hi =>
    intro a ha
    simp only [mem_range] at ha
    simp only [mem_Icc]
    omega
  case h =>
    intro a ha
    congr 1
    omega
  case i_inj =>
    intro a1 ha1 a2 ha2 heq
    omega
  case i_surj =>
    intro b hb
    simp only [mem_Icc] at hb
    refine ⟨b - (N - K), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega

/-- LEAF p. 291, display (7) and the line above it: `S(K) ~ K² N` from the Theorem when
`J(N, K) = o(K² N)`. The range is the Theorem's, `1 ≤ K ≤ N / log³ N`, which also excludes
`K = 0`, where both quotients are `0`. `K → ∞` is needed for the Theorem's `O(K N)` term. It is
implied in the paper: for bounded `K` most `x ≤ N` have no prime in `(x, x + K]`, so `J` is about
`K² N`. -/
theorem leaf_fejer_asymp (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hinf : Tendsto K atTop atTop) :
    Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) →
    Tendsto (fun N : ℕ => fejer N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 1) := by
  intro hJ
  obtain ⟨C, hC, hT⟩ := theorem6_proved
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N0, hN0⟩ := hT (δ / 3) (by positivity)
  have e1 : ∀ᶠ N : ℕ in atTop, Jg N (K N) / ((K N : ℝ) ^ 2 * N) < δ / 3 :=
    hJ.eventually (Iio_mem_nhds (by positivity))
  have e2 : ∀ᶠ N : ℕ in atTop, C * ((K N : ℝ))⁻¹ < δ / 3 := by
    have h1 : Tendsto (fun N : ℕ => ((K N : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hinf)
    have h2 : Tendsto (fun N : ℕ => C * ((K N : ℝ))⁻¹) atTop (nhds (C * 0)) :=
      tendsto_const_nhds.mul h1
    rw [mul_zero] at h2
    exact h2.eventually (Iio_mem_nhds (by positivity))
  have e3 : ∀ᶠ N : ℕ in atTop, N0 ≤ N := eventually_ge_atTop N0
  obtain ⟨M, hM⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and hK)))
  refine ⟨M, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3, h4a, h4b⟩ := hM N hN
  have hKpos : (0 : ℝ) < K N := by exact_mod_cast h4a
  -- the range `1 ≤ K ≤ N / log³ N` forces `N > 1`
  have hq : (1 : ℝ) ≤ (N : ℝ) / Real.log N ^ 3 := le_trans (by exact_mod_cast h4a) h4b
  have hL3 : 0 < Real.log N ^ 3 := by
    rcases lt_trichotomy (Real.log N ^ 3) 0 with h | h | h
    · have hle : (N : ℝ) / Real.log N ^ 3 ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) h.le
      linarith
    · rw [h, div_zero] at h4b
      linarith
    · exact h
  have hlogpos : 0 < Real.log N := by
    by_contra h
    push_neg at h
    exact absurd hL3 (not_lt.mpr ((by decide : Odd 3).pow_nonpos h))
  have hN1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp hlogpos
  have hNpos : (0 : ℝ) < N := by linarith
  have hD : 0 < (K N : ℝ) ^ 2 * N := by positivity
  rw [Real.dist_eq]
  have hrw : fejer N (K N) / ((K N : ℝ) ^ 2 * N) - 1 =
      (fejer N (K N) - (K N : ℝ) ^ 2 * N) / ((K N : ℝ) ^ 2 * N) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hD, div_lt_iff₀ hD]
  have hJ' : Jg N (K N) < δ / 3 * ((K N : ℝ) ^ 2 * N) := by
    rwa [div_lt_iff₀ hD] at h1
  have hCK : C * (K N : ℝ) * N < δ / 3 * ((K N : ℝ) ^ 2 * N) := by
    have hm := mul_lt_mul_of_pos_right h2 hD
    have he : C * ((K N : ℝ))⁻¹ * ((K N : ℝ) ^ 2 * N) = C * (K N : ℝ) * N := by
      field_simp
    rwa [he] at hm
  have hT' := hN0 N h3 (K N) h4a h4b
  have heps : δ / 3 * ((K N : ℝ) ^ 2 * N) * 3 = δ * ((K N : ℝ) ^ 2 * N) := by ring
  linarith

/-- PROVED p. 292: `S(K) - S(K - h) ≤ h Σ_{|n| ≤ K} R(N + n)`, so the backward difference quotient
is the lower bound. The old leaf ran the forward difference this way and was false. -/
theorem leaf_sum_R_lower (N K h : ℕ) (hpos : 0 < h) (hK : h ≤ K) (hKN : K ≤ N) :
    (fejer N K - fejer N (K - h)) / (h : ℝ) ≤ ∑ n ∈ Icc (N - K) (N + K), Rg n := by
  rw [Rsum_eq_Icc N K hKN, div_le_iff₀ (by exact_mod_cast hpos), mul_comm]
  exact fejer_diff_lower N K h hK

/-- PROVED p. 292: `h Σ_{|n| ≤ K} R(N + n) ≤ S(K + h) - S(K)`, so the forward difference quotient
is the upper bound. -/
theorem leaf_sum_R_upper (N K h : ℕ) (hpos : 0 < h) (hKN : K ≤ N) :
    ∑ n ∈ Icc (N - K) (N + K), Rg n ≤ (fejer N (K + h) - fejer N K) / (h : ℝ) := by
  rw [Rsum_eq_Icc N K hKN, le_div_iff₀ (by exact_mod_cast hpos), mul_comm]
  exact fejer_diff_upper N K h

/-- The shape of the conclusion of `leaf_sum_R_asymp`, at one `K`: the hypotheses of Corollary 1
give `Σ_{|n| ≤ K} R(N + n) ~ 2 K N`. -/
def SumRAsymp (K : ℕ → ℕ) : Prop :=
  (∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3) →
    Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) →
    Tendsto (fun N : ℕ => (∑ n ∈ Icc (N - K N) (N + K N), Rg n) / (2 * (K N : ℝ) * N)) atTop (nhds 1)

/-- LEAF p. 292: `Σ_{|n| ≤ K} R(N + n) ~ 2 K N`, under the Theorem's range and `J(N, K) = o(K² N)`.
The paper differences `S` at `K ± h`, `h = f(K) K`, so it uses `J` at `K ± h` as well as at `K`; see
QUESTION Q-1610 in STATEMENTS.md. -/
theorem leaf_sum_R_asymp (K : ℕ → ℕ) : SumRAsymp K := sorry

/-- LEAF p. 292: `R` to `r` relabeling gives Corollary 1. OPEN. The old proof was vacuous: its
hypothesis was the false old `leaf_sum_R_asymp`. The hypothesis now carries the range and `J`. -/
theorem leaf_relabel (h_asymp : ∀ K : ℕ → ℕ, SumRAsymp K) : Corollary1 := sorry

theorem assembly_corollary1 : Corollary1 :=
  leaf_relabel leaf_sum_R_asymp

end LeanLab.GoldbachGaps.DecompJ205
