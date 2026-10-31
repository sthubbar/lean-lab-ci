/-
AI-written Lean code, Claude, 2026-10-20, run 20261020T2004Z-7678, unit U-1271.
P0048 A. Dudek, L. Dunn, An Explicit Result for the Sum of Two Almost Primes, arXiv 2602.22720,
Section 3, proof of Theorem 3.3, Case 3, read on arxiv.org/html/2602.22720 this run:
"S(A,z) ≥ 4(N-1)/log² N - (1.182/20^8) N^{0.92} log^8 N > 0 for all N > 10^200".

`DudekDunn2026.case3_at_1e200` had the last inequality at the endpoint `N = 10^200` only.
PROVED here, no cited input:
* `case3_key`: `(1.182/20^8) N^{0.92} log^{10} N ≤ 3.9 N` for every real `N ≥ 10^200`.
* `case3_all`: `0 < 4(N - 1)/log² N - (1.182/20^8) N^{0.92} log^8 N` for every real `N ≥ 10^200`,
  the printed display, MATCH.
Method: with `L = log N`, `L₀ = 200 log 10`, `u = L/L₀ ≥ 1`, `u^{10} ≤ e^{10(u-1)} ≤ e^{0.08(L-L₀)}`
since `10/L₀ ≤ 0.08`, and `e^{0.08 L₀} = 10^{16}`, so everything reduces to the endpoint
`(1.182/20^8) L₀^{10} ≤ 3.9 · 10^{16}`, true value about `1.98 · 10^{16}`.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.DudekDunn2026

open Real

noncomputable section
namespace LeanLab.AlmostPrimes.DDCase3

lemma log_ten_bounds : (2.3 : ℝ) < log 10 ∧ log 10 < 2.30261 := by
  refine ⟨?_, Campbell2026.log_ten_lt⟩
  have h := Real.log_two_gt_d9
  -- 10^50 > 2^166
  have hnn : (2 : ℕ) ^ 166 < 10 ^ 50 := by norm_num
  have hn : (2 : ℝ) ^ 166 < 10 ^ 50 := by exact_mod_cast hnn
  have h' := Real.log_lt_log (by positivity) hn
  rw [Real.log_pow, Real.log_pow] at h'
  push_cast at h'
  nlinarith

/-- `u^{10} ≤ e^{10(u - 1)}` for `u ≥ 0`. -/
lemma pow10_le_exp {u : ℝ} (hu : 0 ≤ u) : u ^ 10 ≤ exp (10 * (u - 1)) := by
  have h1 : u ≤ exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
  have h2 : u ^ 10 ≤ exp (u - 1) ^ 10 := pow_le_pow_left₀ hu h1 10
  rw [← Real.exp_nat_mul] at h2
  push_cast at h2
  exact h2

/-- **Key bound**: `(1.182/20^8) N^{0.92} log^{10} N ≤ 3.9 N` for every real `N ≥ 10^200`. -/
theorem case3_key (N : ℝ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    (1.182 / 20 ^ 8) * N ^ (0.92 : ℝ) * (log N) ^ 10 ≤ 3.9 * N := by
  obtain ⟨hl1, hl2⟩ := log_ten_bounds
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  set L := log N with hLdef
  set L0 := 200 * log 10 with hL0def
  have hL0L : L0 ≤ L := by
    have := Real.log_le_log (by positivity) hN
    rw [Real.log_pow] at this; push_cast at this; simpa [hL0def, hLdef] using this
  have hL0pos : 0 < L0 := by rw [hL0def]; linarith
  have hL0big : 125 ≤ L0 := by rw [hL0def]; linarith
  -- (L/L0)^10 ≤ exp(0.08 (L - L0))
  set u := L / L0 with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hL0pos.le
  have hpow := pow10_le_exp hu0
  have hexp_arg : 10 * (u - 1) ≤ 0.08 * (L - L0) := by
    have e : u - 1 = (L - L0) / L0 := by rw [hu]; field_simp
    rw [e]
    have hd : 0 ≤ L - L0 := by linarith
    rw [mul_div_assoc']
    rw [div_le_iff₀ hL0pos]
    nlinarith
  have hpow2 : u ^ 10 ≤ exp (0.08 * (L - L0)) := hpow.trans (exp_le_exp.mpr hexp_arg)
  have hLu : L ^ 10 = L0 ^ 10 * u ^ 10 := by
    rw [hu, div_pow]; field_simp
  -- the endpoint
  have hend : (1.182 / 20 ^ 8) * L0 ^ 10 ≤ (3.9 : ℝ) * 10 ^ 16 := by
    have : L0 ^ 10 ≤ (200 * 2.30261 : ℝ) ^ 10 := by
      apply pow_le_pow_left₀ hL0pos.le; rw [hL0def]; linarith
    have h2 : (1.182 / 20 ^ 8) * (200 * 2.30261 : ℝ) ^ 10 ≤ 3.9 * 10 ^ 16 := by norm_num
    nlinarith
  have hexp16 : exp (0.08 * L0) = (10 : ℝ) ^ 16 := by
    rw [hL0def, show (0.08 : ℝ) * (200 * log 10) = (16 : ℕ) * log 10 by push_cast; ring,
      Real.exp_nat_mul, exp_log (by norm_num)]
  -- N^0.92 = exp(0.92 L), N = exp L
  have hNr : N ^ (0.92 : ℝ) = exp (0.92 * L) := by
    rw [rpow_def_of_pos hN0, hLdef, mul_comm]
  have hNe : N = exp L := (exp_log hN0).symm
  have hcL : (1.182 / 20 ^ 8) * L ^ 10 ≤ 3.9 * exp (0.08 * L) := by
    rw [hLu]
    have hu10 : 0 ≤ u ^ 10 := pow_nonneg hu0 10
    calc (1.182 / 20 ^ 8) * (L0 ^ 10 * u ^ 10) = ((1.182 / 20 ^ 8) * L0 ^ 10) * u ^ 10 := by ring
      _ ≤ ((3.9 : ℝ) * 10 ^ 16) * exp (0.08 * (L - L0)) :=
          mul_le_mul hend hpow2 hu10 (by norm_num)
      _ = 3.9 * (exp (0.08 * L0) * exp (0.08 * (L - L0))) := by rw [hexp16]; ring
      _ = 3.9 * exp (0.08 * L) := by rw [← exp_add]; ring_nf
  calc (1.182 / 20 ^ 8) * N ^ (0.92 : ℝ) * L ^ 10
      = exp (0.92 * L) * ((1.182 / 20 ^ 8) * L ^ 10) := by rw [hNr]; ring
    _ ≤ exp (0.92 * L) * (3.9 * exp (0.08 * L)) :=
        mul_le_mul_of_nonneg_left hcL (exp_pos _).le
    _ = 3.9 * (exp (0.92 * L) * exp (0.08 * L)) := by ring
    _ = 3.9 * N := by rw [← exp_add, hNe]; ring_nf

/-- **Dudek-Dunn Theorem 3.3, Case 3, the final display, for every `N ≥ 10^200`**:
`4(N - 1)/log² N - (1.182/20^8) N^{0.92} log^8 N > 0`. MATCHES. -/
theorem case3_all (N : ℝ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    0 < 4 * (N - 1) / (log N) ^ 2 - (1.182 / 20 ^ 8) * N ^ (0.92 : ℝ) * (log N) ^ 8 := by
  have hk := case3_key N hN
  have hN1 : (1 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN
  have hlog : 0 < log N := log_pos hN1
  have hl2 : 0 < (log N) ^ 2 := by positivity
  have hbig : (100 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hlt : (1.182 / 20 ^ 8) * N ^ (0.92 : ℝ) * (log N) ^ 10 < 4 * (N - 1) := by linarith
  rw [sub_pos, lt_div_iff₀ hl2]
  calc (1.182 / 20 ^ 8) * N ^ (0.92 : ℝ) * (log N) ^ 8 * (log N) ^ 2
      = (1.182 / 20 ^ 8) * N ^ (0.92 : ℝ) * (log N) ^ 10 := by ring
    _ < 4 * (N - 1) := hlt

#print axioms case3_key
#print axioms case3_all

end LeanLab.AlmostPrimes.DDCase3
