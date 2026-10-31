/-
P0069 Baker, Harman, Pintz 1997, Lemma 5, end of its proof, page 21, read from the page images
papers/P0069-original.pdf. Unit U-5156, CLOUD 20261019T0213Z-cloud14.

PROVED, the last two steps of the partial summation: `term_eq`, `M^{-1/2}(M/n)^{1/2} = n^{-1/2}`, with
`n = p₁⋯p_{r-1}`; `sum_inv_sqrt_le`, `Σ_{1 ≤ n ≤ K} n^{-1/2} ≤ 2K^{1/2}`, so the sum over `n ≪ M` is
`≪ M^{1/2}`. All MATCH. U-5161: `residue_le`, `residue_saving`, the residue at `1 - it` is `≤ 3N/|t| ≤ 3Nℒ^{-A}`, MATCH. U-5162: `horiz_power`, the size of the integrand on the horizontal segments. U-5159, the vertical integral: `vertical_ok`, `vertical_ok_tendsto`, with
`log N ≥ ℒ^{9/10}` the factor `exp(-ε log N/(2ℒ^{4/5}))` beats every power of `ℒ`; FINDING F-5024, cosmetic,
falsifier AGREE: the page prints `N ≥ ℒ^{9/10}`, under which `vertical_printed_fails` shows no saving, and
cites (3.31) for `z` where (3.32), `z ≥ exp(ℒ^{9/10})`, is meant. The large sieve type input giving `L^{-A}` is not formalized here.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma5
open Finset

theorem term_eq {M n : ℝ} (hM : 0 < M) (hn : 0 < n) :
    1 / Real.sqrt M * Real.sqrt (M / n) = 1 / Real.sqrt n := by
  have h1 := (Real.sqrt_pos.mpr hM).ne'
  have h2 := (Real.sqrt_pos.mpr hn).ne'
  rw [Real.sqrt_div hM.le]
  field_simp

theorem sum_inv_sqrt_le (K : ℕ) :
    ∑ n ∈ Icc 1 K, 1 / Real.sqrt n ≤ 2 * Real.sqrt K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_Icc_succ_top (by omega), Nat.cast_succ]
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    set a := Real.sqrt (K : ℝ)
    set b := Real.sqrt ((K : ℝ) + 1)
    have ha : 0 ≤ a := Real.sqrt_nonneg _
    have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
    have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
    have ha2 : a ^ 2 = K := Real.sq_sqrt hK
    have hb2 : b ^ 2 = (K : ℝ) + 1 := Real.sq_sqrt (by linarith)
    have key : 1 / b ≤ 2 * (b - a) := by
      rw [div_le_iff₀ hb]
      nlinarith
    linarith

/-! ### The vertical integral, U-5159

The proof bounds the vertical integral by `ℒ³N exp(-ε log N/(2ℒ^{4/5}))` and needs it `≪ Nℒ^{-A}`. -/

/-- With `log N ≥ ℒ^{9/10}`, as `z ≥ exp(ℒ^{9/10})` of (3.32) gives for `N ≥ z`, the exponent is at least
`εℒ^{1/10}/2`, which beats every power of `ℒ`. -/
theorem vertical_ok {ℒ N ε : ℝ} (hℒ : 0 < ℒ) (hε : 0 ≤ ε) (hN : ℒ ^ (9 / 10 : ℝ) ≤ Real.log N) :
    ε * ℒ ^ (1 / 10 : ℝ) / 2 ≤ ε * Real.log N / (2 * ℒ ^ (4 / 5 : ℝ)) := by
  have hp : 0 < ℒ ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hℒ _
  have hsplit : ℒ ^ (9 / 10 : ℝ) = ℒ ^ (1 / 10 : ℝ) * ℒ ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_add hℒ]; norm_num
  rw [le_div_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left hN hε
  rw [hsplit] at this
  nlinarith

theorem vertical_ok_tendsto {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    Filter.Tendsto (fun ℒ : ℝ => ℒ ^ (3 + A) * Real.exp (-(ε * ℒ ^ (1 / 10 : ℝ) / 2)))
      Filter.atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * (3 + A)) (ε / 2) (by linarith)).comp
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num))
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with ℒ hℒ
  simp only [Function.comp]
  rw [← Real.rpow_mul hℒ.le]
  congr 1
  · norm_num; ring_nf
  · congr 1; ring

/-- As printed, `N ≥ ℒ^{9/10}`: at `N = ℒ^{9/10}`, `ℒ ≥ 1`, `0 ≤ ε ≤ 1`, the exponent is at most
`9/16`, so the factor is at least `e^{-9/16} > 1/2` and the bound is `≫ ℒ³N`, no saving. -/
theorem vertical_printed_fails {ℒ ε : ℝ} (hℒ : 1 ≤ ℒ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε * Real.log (ℒ ^ (9 / 10 : ℝ)) / (2 * ℒ ^ (4 / 5 : ℝ)) ≤ 9 / 16 := by
  have hℒ0 : 0 < ℒ := by linarith
  have hp : 0 < ℒ ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hℒ0 _
  have hlog : Real.log ℒ ≤ ℒ ^ (4 / 5 : ℝ) / (4 / 5) :=
    Real.log_le_rpow_div hℒ0.le (by norm_num)
  have hl0 : 0 ≤ Real.log ℒ := Real.log_nonneg hℒ
  rw [Real.log_rpow hℒ0, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hlog hε, mul_le_mul_of_nonneg_right hε1 hl0]

/-- U-5161, the residue at `1 - it`: `|N'^{1-it} - N^{1-it}|/|1 - it| ≤ 3N/|t|` for `N < N' ≤ 2N`,
so with `|t| ≥ ℒ^A δ_χ` it is `≤ 3Nℒ^{-A}`. -/
theorem residue_le {N N' t : ℝ} (hN : 0 < N) (hN' : N' ≤ 2 * N) (hNN : N < N') (ht : t ≠ 0) :
    ‖(N' : ℂ) ^ (1 - t * Complex.I) - (N : ℂ) ^ (1 - t * Complex.I)‖ / ‖1 - t * Complex.I‖ ≤
      3 * N / |t| := by
  have hN'0 : 0 < N' := by linarith
  have h1 : ‖(N' : ℂ) ^ (1 - t * Complex.I)‖ = N' := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN'0]; simp
  have h2 : ‖(N : ℂ) ^ (1 - t * Complex.I)‖ = N := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]; simp
  have hnum : ‖(N' : ℂ) ^ (1 - t * Complex.I) - (N : ℂ) ^ (1 - t * Complex.I)‖ ≤ 3 * N := by
    calc _ ≤ ‖(N' : ℂ) ^ (1 - t * Complex.I)‖ + ‖(N : ℂ) ^ (1 - t * Complex.I)‖ := norm_sub_le _ _
      _ ≤ 3 * N := by rw [h1, h2]; linarith
  have hden : |t| ≤ ‖1 - t * Complex.I‖ := by
    have := Complex.abs_im_le_norm (1 - t * Complex.I)
    simpa using this
  have ht0 : 0 < |t| := abs_pos.mpr ht
  calc _ ≤ 3 * N / ‖1 - t * Complex.I‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ 3 * N / |t| := div_le_div_of_nonneg_left (by linarith) ht0 hden

theorem residue_saving {N t ℒ A : ℝ} (hN : 0 ≤ N) (hℒ : 0 < ℒ) (ht : ℒ ^ A ≤ |t|) :
    3 * N / |t| ≤ 3 * N * ℒ ^ (-A) := by
  have hp : 0 < ℒ ^ A := Real.rpow_pos_of_pos hℒ A
  rw [Real.rpow_neg hℒ.le, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (by linarith) hp ht

/-- U-5162, the horizontal segments: for `Re w = σ ≤ 1 + ℒ^{-1}`, `ℒ = log x`, and `1 ≤ 2N ≤ x`,
`(2N)^σ ≤ e · 2N`, since `x^{1/log x} = e`; so with `|w| ≥ x/2` and the `O(ℒ²)` bound on the
integrand the horizontal integrals are `O(Nℒ²/x)`. -/
theorem horiz_power {N σ x : ℝ} (hN : 1 ≤ 2 * N) (h2N : 2 * N ≤ x) (hx : 1 < x)
    (hσ : σ ≤ 1 + 1 / Real.log x) : (2 * N) ^ σ ≤ Real.exp 1 * (2 * N) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have h2N0 : 0 < 2 * N := by linarith
  calc (2 * N) ^ σ ≤ (2 * N) ^ (1 + 1 / Real.log x) := Real.rpow_le_rpow_of_exponent_le hN hσ
    _ = (2 * N) * (2 * N) ^ (1 / Real.log x) := by
      rw [Real.rpow_add h2N0, Real.rpow_one]
    _ ≤ (2 * N) * x ^ (1 / Real.log x) := by
      gcongr
    _ = (2 * N) * Real.exp 1 := by
      rw [Real.rpow_def_of_pos (by linarith), mul_one_div_cancel hlx.ne']
    _ = Real.exp 1 * (2 * N) := by ring

end LeanLab.BHP1997.Lemma5
