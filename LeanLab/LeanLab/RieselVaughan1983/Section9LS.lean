/-
P0032 Riesel-Vaughan 1983, Section 9, pages 69 and 70, redone with the weaker Lemma 14 of
Lemma13LS.lean, and the 18-prime Theorem with no Montgomery-Vaughan input.
Unit U-6713, CLOUD 20261020T1816Z-cloud48, track T1. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

Lemma 14 now reads `Ψ_k ≥ (C/15)((8 + log 5/L) S_k² − (y/L)(76/75 + 10.5/L) S_k)`, so the
bracket of page 69 starts at `8 − 76/75 = 524/75 ≈ 6.9867` instead of `7`. The three numerical
steps become
* `sec9_step1LS`: `(8 + log 5/L)(1 − 3.6581/L) − (76/75 + 10.5/L) ≥ 524/75 − 38.2/L`,
* `sec9_step2LS`: `(524/75 − 38.2/L)(1 − 3.6581/L) ≥ 524/75 − 63.8/L`,
* `sec9_step3LS`: `(524/75 − 63.8/L)(1 + 6.8986/L) > 524/75 − 16.9/L ≥ 6.9` for `L ≥ 350`,
and `6.9 · 200/120 = 11.5 > 201/18 ≈ 11.17` gives (9.1); the paper has 6.974 here and needs
more than 6.7.

What is here:
PROVED unconditional: the three steps above.
CONDITIONAL, counted apart:
* `display91LS_of`: (9.1) CONDITIONAL ON Lemma 9, Lemma 6 (i) and (ii) and `Lemma14LSP`.
* `theorem_LS`: **the Theorem**, every even number is a sum of at most eighteen primes,
  CONDITIONAL ON Lemma 5 at five rows, Lemma 6 (i) and (ii), (2.30) and (2.31) and
  Rosser-Schoenfeld (3.3) only. Lemma 14 is `Lemma13LS.lemma14LS`, PROVED, so neither
  Montgomery-Vaughan's (8.17) nor their Lemmas 3 and 8 are used.
* `corollary19_LS`: the nineteen prime form under the same inputs.
KNOWN mathematics.
-/
import LeanLab.RieselVaughan1983.Lemma13LS

open Finset Real

namespace LeanLab.RieselVaughan1983.Section9LS

open LeanLab.RieselVaughan1983 LeanLab.RieselVaughan1983.Lemma13LS

/-- Page 69, first display, new constants:
`(8 + log 5/L)(1 − 3.6581/L) − (76/75 + 10.5/L) ≥ 524/75 − 38.2/L`. -/
lemma sec9_step1LS (L : ℝ) (hL : 350 ≤ L) :
    524 / 75 - 382 / 10 / L ≤
      (8 + Real.log 5 / L) * (1 - 36581 / 10000 / L) - (76 / 75 + 105 / 10 / L) := by
  obtain ⟨h1, h2⟩ := log_5_bounds
  have hL0 : 0 < L := by linarith
  have e : (8 + Real.log 5 / L) * (1 - 36581 / 10000 / L) - (76 / 75 + 105 / 10 / L) =
      524 / 75 + (Real.log 5 - 8 * (36581 / 10000) - 105 / 10) / L -
        Real.log 5 * (36581 / 10000) / L ^ 2 := by field_simp; ring
  rw [e]
  have hq : Real.log 5 * (36581 / 10000) / L ^ 2 ≤
      160944 / 100000 * (36581 / 10000) / 350 / L := by
    rw [div_div, pow_two]
    calc Real.log 5 * (36581 / 10000) / (L * L) ≤
          160944 / 100000 * (36581 / 10000) / (L * L) := by gcongr
      _ ≤ 160944 / 100000 * (36581 / 10000) / (350 * L) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
  have hl : (160943 / 100000 - 8 * (36581 / 10000) - 105 / 10) / L ≤
      (Real.log 5 - 8 * (36581 / 10000) - 105 / 10) / L :=
    div_le_div_of_nonneg_right (by linarith) hL0.le
  have hsum : -((160943 / 100000 - 8 * (36581 / 10000) - 105 / 10) / L) +
      160944 / 100000 * (36581 / 10000) / 350 / L ≤ 382 / 10 / L := by
    rw [show -((160943 / 100000 - 8 * (36581 / 10000) - 105 / 10) / L) +
      160944 / 100000 * (36581 / 10000) / 350 / L = (-(160943 / 100000 - 8 * (36581 / 10000) -
        105 / 10) + 160944 / 100000 * (36581 / 10000) / 350) / L by ring]
    apply div_le_div_of_nonneg_right _ hL0.le
    norm_num
  linarith

/-- Page 69, second display, new constants: `(524/75 − 38.2/L)(1 − 3.6581/L) ≥ 524/75 − 63.8/L`. -/
theorem sec9_step2LS (L : ℝ) (hL : 350 ≤ L) :
    524 / 75 - 638 / 10 / L ≤ (524 / 75 - 382 / 10 / L) * (1 - 36581 / 10000 / L) := by
  have hL0 : 0 < L := by linarith
  rw [show (524 / 75 - 382 / 10 / L) * (1 - 36581 / 10000 / L) =
      524 / 75 - (382 / 10 + 524 / 75 * (36581 / 10000)) / L +
        382 / 10 * (36581 / 10000) / L ^ 2 by field_simp; ring]
  have : 0 ≤ 382 / 10 * (36581 / 10000) / L ^ 2 := by positivity
  have h2 : (382 / 10 + 524 / 75 * (36581 / 10000) : ℝ) ≤ 638 / 10 := by norm_num
  have : (382 / 10 + 524 / 75 * (36581 / 10000)) / L ≤ 638 / 10 / L :=
    div_le_div_of_nonneg_right h2 hL0.le
  linarith

/-- Page 70, new constants: `(524/75 − 63.8/L)(1 + 6.8986/L) > 524/75 − 16.9/L ≥ 6.9`. -/
theorem sec9_step3LS (L : ℝ) (hL : 350 ≤ L) :
    524 / 75 - 169 / 10 / L < (524 / 75 - 638 / 10 / L) * (1 + 68986 / 10000 / L) ∧
      (69 / 10 : ℝ) ≤ 524 / 75 - 169 / 10 / L := by
  have hL0 : 0 < L := by linarith
  constructor
  · rw [show (524 / 75 - 638 / 10 / L) * (1 + 68986 / 10000 / L) =
        524 / 75 - (638 / 10 - 524 / 75 * (68986 / 10000)) / L -
          638 / 10 * (68986 / 10000) / L ^ 2 by field_simp; ring]
    have hq : 638 / 10 * (68986 / 10000) / L ^ 2 ≤
        638 / 10 * (68986 / 10000) / 350 / L := by
      rw [div_div, pow_two]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    have : (638 / 10 - 524 / 75 * (68986 / 10000)) / L +
        638 / 10 * (68986 / 10000) / 350 / L < 169 / 10 / L := by
      rw [← add_div]
      exact div_lt_div_of_pos_right (by norm_num) hL0
    linarith
  · have : 169 / 10 / L ≤ 169 / 10 / 350 := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) hL
    have h2 : (69 / 10 : ℝ) ≤ 524 / 75 - 169 / 10 / 350 := by norm_num
    linarith

set_option maxHeartbeats 2000000 in
/-- **(9.1)** from Lemma 9 and the weaker Lemma 14, CONDITIONAL ON Lemma 9, Lemma 6 (i) and
(ii) through Lemma 15, and `Lemma14LSP`. A copy of `display91_of` with the new constants. -/
theorem display91LS_of (h9 : Lemma9P) (h14 : Lemma14LSP) (h6 : Lemma6i) (h6' : Lemma6ii) :
    Display91 := by
  intro x hx
  rcases le_or_gt x 0 with hneg | hx0
  · have h1 : NCount x = 0 := by
      unfold NCount; rw [Nat.floor_eq_zero.mpr (by linarith)]; rfl
    have h2 : NCount (x / 202) = 0 := by
      unfold NCount; rw [Nat.floor_eq_zero.mpr (by linarith)]; rfl
    rw [h1, h2]
    rcases hneg.lt_or_eq with h | h
    · simp; linarith
    · rw [h] at hx; simp at hx; linarith
  set y := x / 202 with hy
  have hy0 : 0 < y := by positivity
  have hlog202 : Real.log 202 < 6 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]; linarith [exp_six_gt]
  have hLy : Real.log y = Real.log x - Real.log 202 := Real.log_div hx0.ne' (by norm_num)
  set L := Real.log y with hLdef
  have hL350 : 350 < L := by rw [hLy]; linarith
  have hL0 : 0 < L := by linarith
  have hC := Ctw_pos
  set σ := ∑ k ∈ Icc 1 200, Sk y k with hσ
  have h15 := lemma15 h6 h6' y hy0 hL350.le
  rw [← hσ] at h15
  set σ0 := 200 * y / L * (1 - 36581 / 10000 / L) with hσ0
  have hσ0pos : 0 < σ0 := by
    rw [hσ0]
    have : 36581 / 10000 / L < 1 := by rw [div_lt_one hL0]; linarith
    have : 0 < 1 - 36581 / 10000 / L := by linarith
    positivity
  have hCS : σ ^ 2 ≤ 200 * ∑ k ∈ Icc 1 200, Sk y k ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Icc 1 200) (f := fun k => Sk y k)
    simpa using this
  set a8 := 8 + Real.log 5 / L with ha8
  set b := y / L * (76 / 75 + 105 / 10 / L) with hb
  have h14s : Ctw / 15 * (a8 * ∑ k ∈ Icc 1 200, Sk y k ^ 2 - b * σ) ≤
      ∑ k ∈ Icc 1 200, PsiK x y k := by
    have := sum_le_sum (fun k hk => h14 x hx0 hL350 k hk)
    rw [← hy] at this
    refine le_trans (le_of_eq ?_) this
    rw [hσ, mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
  have ha8pos : 0 < a8 := by
    have := (log_5_bounds).1; rw [ha8]; positivity
  have hstep1 := sec9_step1LS L hL350.le
  have hbr : y / L * (524 / 75 - 382 / 10 / L) ≤ a8 * σ / 200 - b := by
    have e : a8 * σ0 / 200 - b = y / L * ((8 + Real.log 5 / L) * (1 - 36581 / 10000 / L) -
        (76 / 75 + 105 / 10 / L)) := by rw [hσ0, ha8, hb]; ring
    have : a8 * σ0 / 200 ≤ a8 * σ / 200 := by
      have := mul_le_mul_of_nonneg_left h15.le ha8pos.le; linarith
    have hyL : 0 < y / L := by positivity
    have := mul_le_mul_of_nonneg_left hstep1 hyL.le
    linarith
  have h7pos : 0 < 524 / 75 - 382 / 10 / L := by
    have : 382 / 10 / L < 524 / 75 := by rw [div_lt_iff₀ hL0]; linarith
    linarith
  have hbrpos : 0 < y / L * (524 / 75 - 382 / 10 / L) := by positivity
  have hσpos : 0 < σ := lt_trans hσ0pos h15
  have hPsi1 : Ctw / 15 * (σ * (y / L * (524 / 75 - 382 / 10 / L))) ≤
      ∑ k ∈ Icc 1 200, PsiK x y k := by
    refine le_trans ?_ h14s
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : σ * (a8 * σ / 200 - b) ≤ a8 * ∑ k ∈ Icc 1 200, Sk y k ^ 2 - b * σ := by
      have := mul_le_mul_of_nonneg_left hCS ha8pos.le
      nlinarith
    have := mul_le_mul_of_nonneg_left hbr hσpos.le
    linarith
  have hPsi2 : Ctw / 15 * (200 * y ^ 2 / L ^ 2 * (524 / 75 - 638 / 10 / L)) ≤
      ∑ k ∈ Icc 1 200, PsiK x y k := by
    refine le_trans ?_ hPsi1
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h2 := sec9_step2LS L hL350.le
    have e : σ0 * (y / L * (524 / 75 - 382 / 10 / L)) = 200 * y ^ 2 / L ^ 2 *
        ((524 / 75 - 382 / 10 / L) * (1 - 36581 / 10000 / L)) := by rw [hσ0]; field_simp
    have h3 : σ0 * (y / L * (524 / 75 - 382 / 10 / L)) ≤
        σ * (y / L * (524 / 75 - 382 / 10 / L)) :=
      mul_le_mul_of_nonneg_right h15.le hbrpos.le
    have h4 : 200 * y ^ 2 / L ^ 2 * (524 / 75 - 638 / 10 / L) ≤ 200 * y ^ 2 / L ^ 2 *
        ((524 / 75 - 382 / 10 / L) * (1 - 36581 / 10000 / L)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hy2 : Real.log (y / 2) = L - Real.log 2 := Real.log_div hy0.ne' (by norm_num)
  have hl2 := Real.log_two_lt_d9
  set D := Real.log (y / 2) * (83 / 10 + Real.log (y / 2)) with hD
  have hDpos : 0 < D := by
    rw [hD, hy2]; have : 0 < L - Real.log 2 := by linarith
    positivity
  have h9x := h9 x hx0 hL350
  rw [← hy, ← hD] at h9x
  have hDL := sec9_logy2 L hL350.le
  rw [← hy2, ← hD] at hDL
  have h3 := sec9_step3LS L hL350.le
  set Δ := (NCount x : ℝ) - NCount y with hΔ
  have hkey : Ctw / 15 * (200 * y ^ 2 / L ^ 2 * (524 / 75 - 638 / 10 / L)) ≤
      Δ * (8 * Ctw * y / D) := le_trans hPsi2 h9x
  have h7' : 0 < 524 / 75 - 638 / 10 / L := by
    have : 638 / 10 / L < 524 / 75 := by rw [div_lt_iff₀ hL0]; linarith
    linarith
  have hfin : 200 * y / 120 * ((524 / 75 - 638 / 10 / L) * (D / L ^ 2)) ≤ Δ := by
    have e : Δ * (8 * Ctw * y / D) = Δ * (8 * Ctw * y) / D := by ring
    rw [e, le_div_iff₀ hDpos] at hkey
    have e2 : 200 * y / 120 * ((524 / 75 - 638 / 10 / L) * (D / L ^ 2)) * (8 * Ctw * y) =
        Ctw / 15 * (200 * y ^ 2 / L ^ 2 * (524 / 75 - 638 / 10 / L)) * D := by
      field_simp; ring
    have hpos : 0 < 8 * Ctw * y := by positivity
    rw [← mul_le_mul_iff_of_pos_right hpos, e2]
    linarith
  have hge : 200 * y / 120 * (69 / 10) ≤
      200 * y / 120 * ((524 / 75 - 638 / 10 / L) * (D / L ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (524 / 75 - 638 / 10 / L) * (1 + 68986 / 10000 / L) ≤
        (524 / 75 - 638 / 10 / L) * (D / L ^ 2) := mul_le_mul_of_nonneg_left hDL.le h7'.le
    linarith [h3.1, h3.2]
  have hxy : x = 202 * y := by rw [hy]; ring
  rw [hxy]
  have : (202 * y - y) / 18 < 200 * y / 120 * (69 / 10) := by nlinarith
  linarith

/-- **The Theorem**, every even number is a sum of at most eighteen primes, CONDITIONAL ON
Lemma 5 at five rows, the four of Lemma 8 and `Lemma5Neg` at `(60, 8.3)`, Lemma 6 (i) and (ii),
(2.30) and (2.31), and Rosser-Schoenfeld (3.3). No Montgomery-Vaughan input: Lemma 13 and
Lemma 14 are `Lemma13LS.lemma13LS` and `Lemma13LS.lemma14LS`, PROVED. -/
theorem theorem_LS (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33) :
    Theorem :=
  theorem_of h24 h42 h278 h396 h6 hTab hRS (display91LS_of (lemma9_of h5) lemma14LS h6 h6')

/-- The nineteen prime form, every `n > 1` is a sum of at most nineteen primes, under the same
inputs. -/
theorem corollary19_LS (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33) :
    Corollary19 :=
  corollary19_of h24 h42 h278 h396 h6 hTab hRS
    (display91LS_of (lemma9_of h5) lemma14LS h6 h6')

end LeanLab.RieselVaughan1983.Section9LS
