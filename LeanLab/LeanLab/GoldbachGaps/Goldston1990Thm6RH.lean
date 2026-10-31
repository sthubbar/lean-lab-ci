import LeanLab.GoldbachGaps.Goldston1990Thm6PNT
import LeanLab.GoldbachGaps.Goldston1990SelbergB

/-!
# Goldston 1990: the Fejér asymptotic under RH, no cited input

Lab proof, unit U-6301, CLOUD 20261020T1017Z-cloud40, P0030. AI wrote this file. Known
mathematics, Goldston 1990 and Selberg 1943.

`fejer_asymp_rh`: under RH, for every `K = K(N)` with `log² N = o(K)` and `K² ≤ N`,
`Σ_{|n| ≤ K} (K - |n|) R(N + n) ~ K² N`. This is the first display of Goldston's Section 5, the
step his Corollaries 1 and 2 start from, now from `theorem6_proved` and the lab's RH bound
`jg_little_o_b`, PROVED CONDITIONAL ON RiemannHypothesis only. Binary Goldbach is OPEN.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset Filter

theorem fejer_asymp_rh (hRH : RiemannHypothesis) (K : ℕ → ℕ)
    (hlog : Tendsto (fun N : ℕ => Real.log N ^ 2 / K N) atTop (nhds 0))
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ K N * K N ≤ N) :
    Tendsto (fun N : ℕ => fejer N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 1) := by
  obtain ⟨C, hC, hT⟩ := theorem6_proved
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N0, hN0⟩ := hT (δ / 3) (by positivity)
  have e1 : ∀ᶠ N : ℕ in atTop, Jg N (K N) / ((K N : ℝ) ^ 2 * N) < δ / 3 :=
    (jg_little_o_b hRH K hlog hK).eventually (Iio_mem_nhds (by positivity))
  have e2 : ∀ᶠ N : ℕ in atTop, Real.log N ^ 2 / K N < δ / (3 * C) :=
    hlog.eventually (Iio_mem_nhds (by positivity))
  have e3 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have e4 := range_of_sq_le K hK
  have e5 : ∀ᶠ N : ℕ in atTop, N0 ≤ N := eventually_ge_atTop N0
  obtain ⟨M, hM⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and e5))))
  refine ⟨M, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3, ⟨h4a, h4b⟩, h5⟩ := hM N hN
  have hT' := hN0 N h5 (K N) h4a h4b
  have hKpos : (0 : ℝ) < K N := by exact_mod_cast h4a
  have hL3 : 0 < Real.log N ^ 3 := pow_pos (by linarith) 3
  have hNpos : (0 : ℝ) < N := by
    have := lt_of_lt_of_le hKpos h4b
    exact (div_pos_iff_of_pos_right hL3).mp this
  have hD : 0 < (K N : ℝ) ^ 2 * N := by positivity
  rw [Real.dist_eq]
  have hrw : fejer N (K N) / ((K N : ℝ) ^ 2 * N) - 1 =
      (fejer N (K N) - (K N : ℝ) ^ 2 * N) / ((K N : ℝ) ^ 2 * N) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hD, div_lt_iff₀ hD]
  have hJ : Jg N (K N) < δ / 3 * ((K N : ℝ) ^ 2 * N) := by
    rwa [div_lt_iff₀ hD] at h1
  have hCK : C < δ / 3 * K N := by
    have h2' := h2
    rw [div_lt_iff₀ hKpos] at h2'
    have hl2 : 1 ≤ Real.log N ^ 2 := by nlinarith
    have : 1 < δ / (3 * C) * K N := by linarith
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)] at this
    linarith
  have hCKN : C * K N * N < δ / 3 * ((K N : ℝ) ^ 2 * N) := by
    have := mul_lt_mul_of_pos_right hCK (show (0 : ℝ) < K N * N by positivity)
    nlinarith
  have hε : δ / 3 * (K N : ℝ) ^ 2 * N = δ / 3 * ((K N : ℝ) ^ 2 * N) := by ring
  rw [hε] at hT'
  linarith

end LeanLab.GoldbachGaps.Goldston1990
