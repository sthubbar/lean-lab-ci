/-
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T1103Z-29422, unit U-1398.
P0020 P. J. Campbell 2026, A Sharper Explicit Result for the Sum of Two Almost Primes,
arXiv 2608.09488 v1, re-read on arxiv.org/html/2608.09488 this run, Section 5, proof of
Theorem 1.2, Case 3, `N ≥ N₁ = 10^132`, `z = N^{1/16.5} ≥ z₁ = 10^8`, `D = z^{14.66}`,
`s = 14.66`, `k = 2 + log 1.097`: Theorem 2.1 gives `S(𝒜, z) ≥ X V(z) F(s, k) - 2 R₄(𝒜, D)`;
with `X ≥ (N - 1)/3`, Lemma 4.2 `V(z) ≥ 1.241/log² z`, `F > 0.0563` and Lemma 4.3
`R₄(𝒜, z^{14.66}) < 0.563 z^{14.66} log^8 z` this is the printed display
`S(𝒜, z) > 6.34 (N - 1)/log² N - 2.05·10^-10 N^{14.66/16.5} log^8 N`.

This module does for `Case3Sieve` what CampbellCase2X did for `Case2Sieve`.

PROVED, no cited input:
* `z_ge_1e8`: `10^8 ≤ N^{1/16.5}` for `N ≥ 10^132`. `log_zOf`: `log z = log N / 16.5`.
  `zOf_rpow`: `z^{14.66} = N^{14.66/16.5}`. `case3_F`: `F(14.66, 2 + log 1.097) > 0.0563`,
  from `Campbell43.case3_const`.
* `case3_main_term`: `6.34 (N - 1)/log² N ≤ X V F` from `X ≥ (N - 1)/3`, `V ≥ 1.241/log² z`,
  `F > 0.0563` and `Campbell2026.case3_main`.
* `case3_error_term`: `2 · 0.563 z^{14.66} log^8 z ≤ 2.05e-10 N^{14.66/16.5} log^8 N`, from
  `Campbell2026.case3_error`.
CONDITIONAL, counted apart:
* `case3Sieve_of`: `CampbellCase3.Case3Sieve` CONDITIONAL ON `Thm21Case3 R4`, `Lemma42` and
  `Lemma43 R4`, for one and the same function `R4`, the remainder `R₄(𝒜, z^{14.66})` as a
  function of `N`; `X ≥ (N - 1)/3` is no longer an input, it is `CampbellCase2X.X_ge`.
* `theorem1_2_of_inputs3`: Theorem 1.2, `Ω(ab) ≤ 33` for every `N ≥ 2`, CONDITIONAL ON
  `GapTable`, `Case2Sieve`, `Case2Table`, `Thm21Case3 R4`, `Lemma42`, `Lemma43 R4`.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.CampbellCase2X
import LeanLab.AlmostPrimes.Campbell43

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.CampbellCase3X
open LeanLab.AlmostPrimes Campbell2026 CampbellCase3 CampbellCase2 CampbellCase2X

/-! ### Named cited inputs -/

/-- Cited: Theorem 2.1 at `s = 14.66`, `k = 2 + log 1.097`, the dimension condition from
Lemma 4.1(2) with `K = 1.097`, for the pre-sieved sequence with `X = |𝒜|`, `z = N^{1/16.5}`,
`D = z^{14.66}`, in the range of Case 3. `R4 N` stands for `R₄(𝒜, z^{14.66})`. -/
def Thm21Case3 (R4 : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, N1 ≤ N →
    (Xcount N : ℝ) * V N (zOf N) * F 14.66 (2 + log 1.097) - 2 * R4 N ≤ (siftCount N (zOf N) : ℝ)

/-- Cited: Lemma 4.2, `V(z) ≥ 1.241/log² z` for `z ≥ z₁ = 10^8`, for every `N`. -/
def Lemma42 : Prop :=
  ∀ N : ℕ, ∀ z : ℝ, (10 : ℝ) ^ 8 ≤ z → 1.241 / (log z) ^ 2 ≤ V N z

/-- Cited: Lemma 4.3, `R₄(𝒜, z^{14.66}) < 0.563 z^{14.66} log^8 z` for `z ≥ z₁`, read at
`z = N^{1/16.5}`, `N ≥ N₁`, and weakened from `<` to `≤`. -/
def Lemma43 (R4 : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, N1 ≤ N → R4 N ≤ 0.563 * zOf N ^ (14.66 : ℝ) * (log (zOf N)) ^ 8

/-! ### The arithmetic, PROVED -/

lemma N_pos {N : ℕ} (hN : N1 ≤ N) : (0 : ℝ) < N := by
  have : 0 < N := lt_of_lt_of_le (show 0 < N1 by unfold N1; norm_num) hN
  exact_mod_cast this

lemma N_ge_real {N : ℕ} (hN : N1 ≤ N) : (10 : ℝ) ^ 132 ≤ N := by
  have h : 10 ^ 132 ≤ N := hN
  exact_mod_cast h

/-- `z = N^{1/16.5} ≥ 10^8` in Case 3. -/
theorem z_ge_1e8 {N : ℕ} (hN : N1 ≤ N) : (10 : ℝ) ^ 8 ≤ zOf N := by
  have h1 := N_ge_real hN
  have e : ((10 : ℝ) ^ 132) ^ (1 / (16.5 : ℝ)) = (10 : ℝ) ^ 8 := by
    rw [← rpow_natCast, ← rpow_mul (by norm_num), ← rpow_natCast]
    norm_num
  rw [← e]; unfold zOf
  exact rpow_le_rpow (by positivity) h1 (by norm_num)

/-- `log z = log N / 16.5`. -/
theorem log_zOf (N : ℕ) : log (zOf N) = log N / 16.5 := by
  unfold zOf
  rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).eq_or_lt with h | h
  · rw [← h, zero_rpow (by norm_num)]; simp
  · rw [log_rpow h]; ring

/-- `z^{14.66} = N^{14.66/16.5}`. -/
theorem zOf_rpow (N : ℕ) : zOf N ^ (14.66 : ℝ) = (N : ℝ) ^ (14.66 / 16.5 : ℝ) := by
  unfold zOf
  rw [← rpow_mul (Nat.cast_nonneg N)]
  norm_num

/-- `F(14.66, 2 + log 1.097) > 0.0563`, the bracketed factor of Case 3. MATCHES. -/
theorem case3_F : (0.0563 : ℝ) < F 14.66 (2 + log 1.097) := by
  unfold F
  exact Campbell43.case3_const

/-- **Main term:** `6.34 (N - 1)/log² N ≤ X V(z) F`, from `X_ge` and Lemma 4.2. -/
theorem case3_main_term (h42 : Lemma42) {N : ℕ} (hN : N1 ≤ N) :
    6.34 * ((N : ℝ) - 1) / (log N) ^ 2 ≤
      (Xcount N : ℝ) * V N (zOf N) * F 14.66 (2 + log 1.097) := by
  have hN1 : 1 ≤ N := le_trans (show 1 ≤ N1 by unfold N1; norm_num) hN
  have hX := X_ge_real hN1
  have hNr := N_ge_real hN
  have hNm : 0 ≤ (N : ℝ) - 1 := by
    have : (1 : ℝ) ≤ 10 ^ 132 := by norm_num
    linarith
  have hlogN : 0 < log (N : ℝ) := log_pos (by linarith [show (1 : ℝ) < 10 ^ 132 by norm_num])
  have hV := h42 N (zOf N) (z_ge_1e8 hN)
  rw [log_zOf] at hV
  have hV' : 1.241 * 16.5 ^ 2 / (log N) ^ 2 ≤ V N (zOf N) := by
    have e : (1.241 : ℝ) / (log N / 16.5) ^ 2 = 1.241 * 16.5 ^ 2 / (log N) ^ 2 := by
      field_simp
    linarith
  have hF := case3_F
  have hL2 : 0 < (log (N : ℝ)) ^ 2 := by positivity
  have hVpos : 0 ≤ 1.241 * 16.5 ^ 2 / (log (N : ℝ)) ^ 2 := by positivity
  -- (N - 1)/3 · (1.241·16.5²/L²) · 0.0563 ≤ X V F
  have step : ((N : ℝ) - 1) / 3 * (1.241 * 16.5 ^ 2 / (log N) ^ 2) * 0.0563 ≤
      (Xcount N : ℝ) * V N (zOf N) * F 14.66 (2 + log 1.097) := by
    apply mul_le_mul _ hF.le (by norm_num)
    · exact mul_nonneg (Nat.cast_nonneg _) (le_trans hVpos hV')
    · exact mul_le_mul hX hV' hVpos (Nat.cast_nonneg _)
  have hm := case3_main
  have e2 : ((N : ℝ) - 1) / 3 * (1.241 * 16.5 ^ 2 / (log N) ^ 2) * 0.0563 =
      (1.241 * 16.5 ^ 2 * 0.0563 / 3) * (((N : ℝ) - 1) / (log N) ^ 2) := by
    field_simp
  have hq : 0 ≤ ((N : ℝ) - 1) / (log N) ^ 2 := div_nonneg hNm hL2.le
  have : 6.34 * ((N : ℝ) - 1) / (log N) ^ 2 ≤
      (1.241 * 16.5 ^ 2 * 0.0563 / 3) * (((N : ℝ) - 1) / (log N) ^ 2) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hm.le hq
  linarith

/-- **Error term:** `2 · 0.563 z^{14.66} log^8 z ≤ 2.05e-10 N^{14.66/16.5} log^8 N`. -/
theorem case3_error_term (N : ℕ) :
    2 * (0.563 * zOf N ^ (14.66 : ℝ) * (log (zOf N)) ^ 8) ≤
      2.05e-10 * (N : ℝ) ^ (14.66 / 16.5 : ℝ) * (log N) ^ 8 := by
  rw [zOf_rpow, log_zOf]
  have hA : 0 ≤ (N : ℝ) ^ (14.66 / 16.5 : ℝ) * (log N) ^ 8 := by
    have := rpow_nonneg (Nat.cast_nonneg N) (14.66 / 16.5 : ℝ)
    positivity
  have e : 2 * (0.563 * (N : ℝ) ^ (14.66 / 16.5 : ℝ) * (log N / 16.5) ^ 8) =
      (2 * 0.563 / 16.5 ^ 8) * ((N : ℝ) ^ (14.66 / 16.5 : ℝ) * (log N) ^ 8) := by
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_right case3_error.le hA
  linarith

/-! ### The reduction -/

/-- **`Case3Sieve`, CONDITIONAL ON `Thm21Case3 R4`, `Lemma42` and `Lemma43 R4`.** -/
theorem case3Sieve_of (R4 : ℕ → ℝ) (h21 : Thm21Case3 R4) (h42 : Lemma42) (h43 : Lemma43 R4) :
    Case3Sieve := by
  intro N hN
  have hs := h21 N hN
  have hm := case3_main_term h42 hN
  have he := case3_error_term N
  have hr := h43 N hN
  have : (siftCount N ((N : ℝ) ^ (1 / (16.5 : ℝ))) : ℝ) = (siftCount N (zOf N) : ℝ) := rfl
  rw [this]
  linarith

/-- **Theorem 1.2, CONDITIONAL ON `GapTable`, `Case2Sieve`, `Case2Table`, `Thm21Case3 R4`,
`Lemma42` and `Lemma43 R4`.** -/
theorem theorem1_2_of_inputs3 (hG : GapTable) (hs : Case2Sieve) (ht : Case2Table)
    (R4 : ℕ → ℝ) (h21 : Thm21Case3 R4) (h42 : Lemma42) (h43 : Lemma43 R4) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N :=
  theorem1_2_of_inputs hG hs ht (case3Sieve_of R4 h21 h42 h43)

/-! ### Vacuity checks: each named input on its own can hold -/

/-- `Lemma43` holds for `R4 = 0`. -/
theorem lemma43_zero : Lemma43 (fun _ => 0) := by
  intro N _
  have h0 : 0 ≤ zOf N := rpow_nonneg (Nat.cast_nonneg N) _
  have := rpow_nonneg h0 (14.66 : ℝ)
  show (0 : ℝ) ≤ _
  positivity

/-- `Thm21Case3` holds for `R4 N = X V F / 2` when `F > 0`; jointly with `Lemma43` it is the
paper's content. -/
theorem thm21_trivial :
    Thm21Case3 (fun N => (Xcount N : ℝ) * V N (zOf N) * F 14.66 (2 + log 1.097) / 2) := by
  intro N _
  have : (0 : ℝ) ≤ (siftCount N (zOf N) : ℝ) := Nat.cast_nonneg _
  simp only
  linarith

end LeanLab.AlmostPrimes.CampbellCase3X
