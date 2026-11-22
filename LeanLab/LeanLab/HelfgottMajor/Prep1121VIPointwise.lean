import LeanLab.HelfgottMajor.Prep1121VIPointwiseA

/-!
PREP 2026-11-21, route step `MainLemma41Split123.vertical_integral_bound`, part B.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 34, displays 4.11
and 4.12: the pointwise bound |L'/L(s, χ)| ≤ |log(q/π)| + (1/2) log(τ² + 9/4) + 4.1396 on
s = -1/2 + iτ, assembled in `pointwise_4_12` without sorry of its own.

REPAIR of the written proof, recorded as a QUESTION: the paper bounds |log(3/2 - iτ)| by
log|3/2 + iτ|, which drops the argument, up to π/2. The bound 4.12 is still true: the
argument of log(3/2 - iτ) cancels against the imaginary part of (π/2) cot(π(s+κ)/2), and
|-log(3/2 - iτ) + (π/2) cot(π(s+κ)/2)| ≤ log|3/2 - iτ| + π/2 exactly when
arctan(2|τ|/3) ≤ π tanh(π|τ|). Leaves `log_cot_cancel` and `arctan_le_pi_tanh`.

DECISION: the Dirichlet series constant 1.50524 of display 4.11 is used here as 1.50527,
which still gives 10/27 + log 2 + π/2 + 1.50527 ≤ 4.1396, so that the Euler-Maclaurin
leaves have margins near 1e-5 instead of 5e-6. AI wrote this Lean code. Binary Goldbach is
open.
-/

namespace LeanLab.HelfgottMajor.Prep1121VIPointwise
open Complex MeasureTheory Set
open LeanLab.HelfgottMajor.Prep1121VIPointwiseA

/-- LEAF: P0014 page 34, after display 4.10, repaired: the elementary inequality
arctan(2t/3) ≤ π tanh(πt) for t ≥ 0, which is what makes the argument of log(3/2 - iτ) cancel
against the cotangent term. Numerically the ratio of the two sides is at most 0.22.
Class EASY: arctan x ≤ x, tanh y ≥ y/(1+y), and arctan ≤ π/2 for t above 1/2.
PROVED here. -/
theorem arctan_le_pi_tanh (t : ℝ) (ht : 0 ≤ t) :
    Real.arctan (2 * t / 3) ≤ Real.pi * Real.tanh (Real.pi * t) := by
  have hpi := Real.pi_gt_three
  set y := Real.pi * t with hy
  have hy0 : 0 ≤ y := by positivity
  have hey : 0 < Real.exp y := Real.exp_pos y
  have htanh : Real.tanh y = (Real.exp y * Real.exp y - 1) / (Real.exp y * Real.exp y + 1) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
    field_simp
  have hE : 1 + 2 * y ≤ Real.exp y * Real.exp y := by
    rw [← Real.exp_add]; linarith [Real.add_one_le_exp (y + y)]
  have hlow : y / (1 + y) ≤ Real.tanh y := by
    rw [htanh, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  by_cases h : t ≤ 1 / 2
  · have ha : Real.arctan (2 * t / 3) ≤ 2 * t / 3 := Real.arctan_le_self (by positivity)
    have key : 2 * t / 3 ≤ Real.pi * (y / (1 + y)) := by
      rw [show Real.pi * (y / (1 + y)) = Real.pi * y / (1 + y) by ring,
        le_div_iff₀ (by positivity), hy]
      have h1 : Real.pi * t * t ≤ Real.pi * t * (1 / 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hpi.le)]
    calc Real.arctan (2 * t / 3) ≤ 2 * t / 3 := ha
      _ ≤ Real.pi * (y / (1 + y)) := key
      _ ≤ Real.pi * Real.tanh y := mul_le_mul_of_nonneg_left hlow Real.pi_pos.le
  · rw [not_le] at h
    have hy1 : 1 ≤ y := by rw [hy]; nlinarith
    have hhalf : 1 / 2 ≤ Real.tanh y := by
      refine le_trans ?_ hlow
      rw [le_div_iff₀ (by positivity)]; linarith
    calc Real.arctan (2 * t / 3) ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two _).le
      _ = Real.pi * (1 / 2) := by ring
      _ ≤ Real.pi * Real.tanh y := mul_le_mul_of_nonneg_left hhalf Real.pi_pos.le

/- Helpers for `log_cot_cancel`, ported from the downstream file
`LeanLab.HelfgottMajor.Prep1121DLogCot` (which imports this file, so it cannot be imported here). -/

private theorem arg_line (τ : ℝ) :
    Complex.arg (1 - ((-1 / 2 : ℂ) + τ * I)) = -Real.arctan (2 * τ / 3) := by
  have hx : 1 - ((-1 / 2 : ℂ) + τ * I) = ((3 / 2 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I := by
    push_cast; ring
  have hre : 0 ≤ (((3 / 2 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I).re := by simp; norm_num
  have him : (((3 / 2 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I).im = -τ := by simp
  rw [hx, Complex.arg_of_re_nonneg hre, him, Complex.norm_add_mul_I, Real.arctan_eq_arcsin,
    ← Real.arcsin_neg]
  congr 1
  have h : √(1 + (2 * τ / 3) ^ 2) = (2 / 3) * √((3 / 2) ^ 2 + (-τ) ^ 2) := by
    rw [show 1 + (2 * τ / 3) ^ 2 = (2 / 3) ^ 2 * ((3 / 2) ^ 2 + (-τ) ^ 2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hp : 0 < √((3 / 2 : ℝ) ^ 2 + (-τ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [h]
  field_simp

private theorem cot_gen (x0 y c σ : ℝ) (hc : c ≠ 0) (hσ : σ ^ 2 = 1) (hcos : Real.cos x0 = c)
    (hsin : Real.sin x0 = σ * c) :
    cot (((x0 : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I) =
      ((σ / Real.cosh (2 * y) : ℝ) : ℂ) - I * (Real.tanh (2 * y) : ℂ) := by
  have hC0 : 0 < Real.cosh (2 * y) := Real.cosh_pos _
  have hS : Real.sinh (2 * y) = 2 * Real.sinh y * Real.cosh y := Real.sinh_two_mul y
  have hCC : Real.cosh (2 * y) = Real.cosh y ^ 2 + Real.sinh y ^ 2 := Real.cosh_two_mul y
  have hsq := Real.cosh_sq y
  rw [cot_eq_cos_div_sin, cos_add_mul_I, sin_add_mul_I, ← ofReal_cos, ← ofReal_sin,
    ← ofReal_cosh, ← ofReal_sinh, hcos, hsin, Real.tanh_eq_sinh_div_cosh]
  generalize Real.cosh y = ch at *
  generalize Real.sinh y = sh at *
  generalize Real.cosh (2 * y) = C at *
  generalize Real.sinh (2 * y) = S at *
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ
  have hch0 : ch ≠ 0 := by rintro rfl; nlinarith
  have hne : (((σ * c : ℝ) : ℂ) * ((ch : ℝ) : ℂ) + ((c : ℝ) : ℂ) * ((sh : ℝ) : ℂ) * I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.mul_im, Complex.zero_re] at h'
    have h2 : σ * c * ch = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h3 | h3
      · exact hσ0 h3
      · exact hc h3
    · exact hch0 h1
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
  have hσ' : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hS' : (S : ℂ) = 2 * sh * ch := by exact_mod_cast hS
  have hCC' : (C : ℂ) = ch ^ 2 + sh ^ 2 := by exact_mod_cast hCC
  have hsq' : (ch : ℂ) ^ 2 = sh ^ 2 + 1 := by exact_mod_cast hsq
  have key : (C : ℂ) * ((c : ℂ) * ch - ((σ * c : ℝ) : ℂ) * sh * I) =
      ((σ : ℂ) - I * S) * (((σ * c : ℝ) : ℂ) * ch + (c : ℂ) * sh * I) := by
    push_cast
    linear_combination (c * ch - σ * c * sh * I) * hCC' + (c * ch + σ * c * sh * I) * hsq'
      - c * ch * hσ' - (c * sh - σ * c * ch * I) * hS' + (c * S * sh) * I_sq
  rw [div_eq_iff hne, show ((σ / C : ℝ) : ℂ) - I * ((S / C : ℝ) : ℂ) =
      ((σ : ℂ) - I * S) / C by push_cast; field_simp, div_mul_eq_mul_div, ← key,
    mul_div_cancel_left₀ _ hCne]

private theorem cot_line (τ : ℝ) (κ : ℕ) (hκ : κ = 0 ∨ κ = 1) :
    ∃ ε : ℝ, ε ^ 2 = 1 ∧
      cot ((Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + κ) / 2) =
        ((ε / Real.cosh (Real.pi * τ) : ℝ) : ℂ) - I * (Real.tanh (Real.pi * τ) : ℂ) := by
  have h2 : (0 : ℝ) < √2 / 2 := by positivity
  rcases hκ with rfl | rfl
  · refine ⟨-1, by norm_num, ?_⟩
    have hz : (Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + ((0 : ℕ) : ℂ)) / 2 =
        ((-(Real.pi / 4) : ℝ) : ℂ) + ((Real.pi * τ / 2 : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hz, cot_gen (-(Real.pi / 4)) (Real.pi * τ / 2) (√2 / 2) (-1) h2.ne' (by norm_num)
      (by rw [Real.cos_neg, Real.cos_pi_div_four])
      (by rw [Real.sin_neg, Real.sin_pi_div_four]; ring),
      show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring]
  · refine ⟨1, by norm_num, ?_⟩
    have hz : (Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + ((1 : ℕ) : ℂ)) / 2 =
        ((Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * τ / 2 : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hz, cot_gen (Real.pi / 4) (Real.pi * τ / 2) (√2 / 2) 1 h2.ne' (by norm_num)
      Real.cos_pi_div_four (by rw [Real.sin_pi_div_four]; ring),
      show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring]

private theorem cancel_real (τ ε : ℝ) (hε : ε ^ 2 = 1)
    (harc : ∀ t : ℝ, 0 ≤ t → Real.arctan (2 * t / 3) ≤ Real.pi * Real.tanh (Real.pi * t)) :
    (Real.pi / 2 * (ε / Real.cosh (Real.pi * τ))) ^ 2 +
        (Real.arctan (2 * τ / 3) - Real.pi / 2 * Real.tanh (Real.pi * τ)) ^ 2 ≤
      (Real.pi / 2) ^ 2 := by
  set y := Real.pi * τ with hy
  set a := Real.arctan (2 * τ / 3) with ha
  set T := Real.tanh y with hT
  have hc : 0 < Real.cosh y := Real.cosh_pos y
  have hsech : (ε / Real.cosh y) ^ 2 = 1 - T ^ 2 := by
    rw [hT, Real.tanh_eq_sinh_div_cosh, div_pow, div_pow, hε]
    have := Real.cosh_sq y
    field_simp
    linarith
  have key : a * (a - Real.pi * T) ≤ 0 := by
    rcases le_total 0 τ with h | h
    · have ha0 : 0 ≤ a := Real.arctan_nonneg.mpr (by linarith)
      have h1 := harc τ h
      exact mul_nonpos_of_nonneg_of_nonpos ha0 (by rw [ha, hT, hy]; linarith)
    · have ha0 : a ≤ 0 := by
        have := Real.arctan_nonneg.mpr (show 0 ≤ 2 * (-τ) / 3 by linarith)
        rw [show 2 * (-τ) / 3 = -(2 * τ / 3) by ring, Real.arctan_neg] at this
        linarith
      have h1 := harc (-τ) (by linarith)
      rw [show 2 * (-τ) / 3 = -(2 * τ / 3) by ring, Real.arctan_neg,
        show Real.pi * -τ = -y by rw [hy]; ring, Real.tanh_neg] at h1
      exact mul_nonpos_of_nonpos_of_nonneg ha0 (by rw [← hT] at h1; linarith)
  rw [mul_pow, hsech]
  nlinarith

/-- LEAF: P0014 page 34, display 4.12, first line, repaired. On s = -1/2 + iτ,
cot(π(s+κ)/2) = ∓ sech(πτ) - i tanh(πτ) for κ = 0, 1, and log(3/2 - iτ) =
log|3/2 - iτ| - i arctan(2τ/3), so -log(1-s) + (π/2) cot(π(s+κ)/2) = -log|1-s| + E with
|E|² = (π/2)² - b² + (a - b)², a = arctan(2τ/3), b = (π/2) tanh(πτ), and |E| ≤ π/2 iff
a ≤ 2b for τ ≥ 0, symmetrically for τ below 0. Class MEDIUM: one idea, explicit real and
imaginary parts of cot and log on the line. -/
theorem log_cot_cancel (τ : ℝ) (κ : ℕ) (hκ : κ = 0 ∨ κ = 1)
    (harc : ∀ t : ℝ, 0 ≤ t → Real.arctan (2 * t / 3) ≤ Real.pi * Real.tanh (Real.pi * t)) :
    ‖-Complex.log (1 - ((-1 / 2 : ℂ) + τ * I)) +
        ((Real.pi / 2 : ℝ) : ℂ) * cot ((Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + κ) / 2)‖ ≤
      Real.log ‖1 - ((-1 / 2 : ℂ) + τ * I)‖ + Real.pi / 2 := by
  obtain ⟨ε, hε, hcot⟩ := cot_line τ κ hκ
  set s : ℂ := (-1 / 2 : ℂ) + τ * I with hs
  set L := Real.log ‖1 - s‖ with hL
  set a := Real.arctan (2 * τ / 3) with ha
  set T := Real.tanh (Real.pi * τ) with hT
  have hlog : Complex.log (1 - s) = (L : ℂ) + ((-a : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.log_re, hL]
    · rw [Complex.log_im, show Complex.arg (1 - s) = -a from arg_line τ]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re]
      ring
  rw [hcot, hlog]
  have hX : -((L : ℂ) + ((-a : ℝ) : ℂ) * I) + ((Real.pi / 2 : ℝ) : ℂ) *
      (((ε / Real.cosh (Real.pi * τ) : ℝ) : ℂ) - I * (T : ℂ)) =
      -(L : ℂ) + (((Real.pi / 2 * (ε / Real.cosh (Real.pi * τ)) : ℝ) : ℂ) +
        ((a - Real.pi / 2 * T : ℝ) : ℂ) * I) := by
    push_cast; ring
  rw [hX]
  have hn : 3 / 2 ≤ ‖1 - s‖ := by
    have h' := Complex.abs_re_le_norm (1 - s)
    have hre : (1 - s).re = 3 / 2 := by simp [hs]; norm_num
    rw [hre] at h'
    norm_num at h' ⊢
    linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hE : ‖(((Real.pi / 2 * (ε / Real.cosh (Real.pi * τ)) : ℝ) : ℂ) +
        ((a - Real.pi / 2 * T : ℝ) : ℂ) * I)‖ ≤ Real.pi / 2 := by
    rw [Complex.norm_add_mul_I]
    rw [Real.sqrt_le_left (by positivity)]
    exact cancel_real τ ε hε harc
  calc ‖-(L : ℂ) + (((Real.pi / 2 * (ε / Real.cosh (Real.pi * τ)) : ℝ) : ℂ) +
        ((a - Real.pi / 2 * T : ℝ) : ℂ) * I)‖
      ≤ ‖-(L : ℂ)‖ + ‖(((Real.pi / 2 * (ε / Real.cosh (Real.pi * τ)) : ℝ) : ℂ) +
        ((a - Real.pi / 2 * T : ℝ) : ℂ) * I)‖ := norm_add_le _ _
    _ ≤ L + Real.pi / 2 := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
        linarith


/- Helpers for `logDeriv_three_half_le`, ported from the downstream file
`LeanLab.HelfgottMajor.Prep1121DThreeHalf` (which imports this file, so it cannot be imported here). -/

private theorem tsum_norm_vonMangoldt_eq :
    ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ =
      ‖deriv riemannZeta (3 / 2) / riemannZeta (3 / 2)‖ := by
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (3 / 2 : ℂ)) (by norm_num)
  have hterm : ∀ n, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n
      = ((‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ : ℝ) :
        ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n),
        ← Complex.ofReal_div,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  rw [← norm_neg, ← neg_div, ← hL, LSeries, tsum_congr hterm, ← Complex.ofReal_tsum,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]

/-- LEAF: P0014 page 34, display 4.11, the comparison of Dirichlet series: on re w = 3/2,
|L'/L(w, χ)| ≤ Σ Λ(n) n^(-3/2) = |ζ'(3/2)/ζ(3/2)|. The comparison is already done in
`LeanLab.Linnik.ExplicitFormula.logDeriv_L_three_half_le` with an unnamed constant; Mathlib's
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div` names it. Class MEDIUM: one idea plus a
Mathlib lookup. -/
theorem logDeriv_three_half_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (τ : ℝ) :
    ‖logDeriv χ.LFunction (1 - ((-1 / 2 : ℂ) + τ * I))‖ ≤
      ‖deriv riemannZeta (3 / 2) / riemannZeta (3 / 2)‖ := by
  rw [← tsum_norm_vonMangoldt_eq]
  have hsum : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hsumN : Summable fun n =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ :=
    summable_norm_iff.mpr hsum
  set s : ℂ := 1 - ((-1 / 2 : ℂ) + τ * I) with hs
  have hre : 1 < s.re := by simp [hs]; norm_num
  have hconv : -deriv χ.LFunction s / χ.LFunction s =
      LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hre
    rw [DirichletCharacter.LFunction_eq_LSeries χ hre]
    convert h.symm using 3
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  have hpt : ∀ n, ‖LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ ≤
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · exact le_rfl
    · have hsr : s.re = (3 / 2 : ℂ).re := by simp [hs]; norm_num
      rw [hsr]
      gcongr
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hsum2 : Summable fun n =>
      ‖LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumN
  rw [logDeriv_apply, ← norm_neg, ← neg_div, hconv, LSeries]
  exact (norm_tsum_le_tsum_norm hsum2).trans (hsum2.tsum_le_tsum hpt hsumN)


open Filter

/- Helpers for `zeta_three_half_ge`: the real Euler-Maclaurin comparison behind P0014
display 4.11. The Dirichlet series for zeta(3/2), certified rational lower bounds for
each of the first 101 terms, and a trapezoid tail estimate written as a telescoping sum. -/

private lemma rpow_three_half (x : ℝ) (hx : 0 < x) :
    x ^ ((3:ℝ)/2) = x * Real.sqrt x := by
  rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

private lemma rpow_neg_three_half (x : ℝ) (hx : 0 < x) :
    x ^ (-(3/2) : ℝ) = 1/(x * Real.sqrt x) := by
  rw [show -(3/2 : ℝ) = -((3:ℝ)/2) by norm_num, Real.rpow_neg hx.le,
    rpow_three_half x hx, one_div]

private lemma zeta_series :
    (riemannZeta (3 / 2)).re
      = ∑' (n : ℕ), (1:ℝ)/(((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1)) := by
  have hs : (1:ℝ) < ((3:ℂ)/2).re := by norm_num
  have h1 : riemannZeta (3/2) = ∑' (n : ℕ), (1:ℂ)/((n : ℂ) + 1) ^ ((3:ℂ)/2) :=
    zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hterm : ∀ n : ℕ, (1:ℂ)/((n : ℂ) + 1) ^ ((3:ℂ)/2)
      = Complex.ofReal ((1:ℝ)/(((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1))) := by
    intro n
    have hbase : ((n:ℂ) + 1) = Complex.ofReal ((n:ℝ)+1) := by push_cast; ring
    have hpow : Complex.ofReal ((n:ℝ)+1) ^ ((3:ℂ)/2)
        = Complex.ofReal (((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1)) := by
      have hexp : ((3:ℂ)/2) = Complex.ofReal ((3:ℝ)/2) := by norm_num
      rw [hexp, ← Complex.ofReal_cpow (show (0:ℝ) ≤ (n:ℝ)+1 by positivity),
        rpow_three_half ((n:ℝ)+1) (show (0:ℝ) < (n:ℝ)+1 by positivity)]
    rw [hbase, hpow, ← Complex.ofReal_one, ← Complex.ofReal_div]
  rw [h1, tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_re]

private lemma summ :
    Summable (fun n : ℕ => (1:ℝ)/(((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1))) := by
  have hb : Summable (fun n : ℕ => (n:ℝ) ^ (-(3/2) : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have h2 := (summable_nat_add_iff 1).mpr hb
  refine h2.congr (fun n => ?_)
  have hx : (0:ℝ) < ((n:ℝ)+1) := by positivity
  rw [Nat.cast_add, Nat.cast_one, rpow_neg_three_half _ hx]

private lemma tendsto_inv_sqrt :
    Tendsto (fun n : ℕ => (Real.sqrt ((n:ℝ)+1))⁻¹) atTop (nhds 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n:ℝ)+1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp h1)

private lemma tendsto_inv_shift :
    Tendsto (fun n : ℕ => (((n:ℝ)+1))⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)

private lemma tendsto_G :
    Tendsto (fun n : ℕ => 2 / Real.sqrt ((n:ℝ)+1) + (1/2)/(((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1)))
      atTop (nhds 0) := by
  have hA := tendsto_inv_sqrt
  have hB := tendsto_inv_shift
  have h1 : Tendsto (fun n : ℕ => (2:ℝ) * (Real.sqrt ((n:ℝ)+1))⁻¹) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hA
  have h2 : Tendsto (fun n : ℕ => (1/2:ℝ) * ((((n:ℝ)+1))⁻¹ * (Real.sqrt ((n:ℝ)+1))⁻¹))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hB.mul hA)
  have h3 := h1.add h2
  simpa [div_eq_mul_inv, mul_add, mul_comm, mul_left_comm, mul_assoc] using h3

private lemma trap_real (x : ℝ) (hx : 1 ≤ x) :
    2 / Real.sqrt x + (1/2)/(x * Real.sqrt x) -
        (2 / Real.sqrt (x + 1) + (1/2)/((x + 1) * Real.sqrt (x + 1))) ≤
      1 / (x * Real.sqrt x) := by
  set a := Real.sqrt x with ha
  set b := Real.sqrt (x + 1) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have haa : a ^ 2 = x := Real.sq_sqrt (by linarith)
  have hbb : b ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hb1 : 0 < b + a := by linarith
  have hba : b - a = 1 / (b + a) := by
    rw [eq_div_iff hb1.ne']
    nlinarith [haa, hbb]
  have hp2 : (a * b) ^ 2 = x * (x + 1) := by rw [mul_pow, haa, hbb]
  have hsq : (2 * x ^ 2 + 2 * x - 1) ^ 2 ≤ (a * b * (2 * x + 1)) ^ 2 := by
    have e : (a * b * (2 * x + 1)) ^ 2 = (a * b) ^ 2 * (2 * x + 1) ^ 2 := by ring
    rw [e, hp2]
    nlinarith [hx, sq_nonneg x, sq_nonneg (x - 1)]
  have hL : 0 ≤ 2 * x ^ 2 + 2 * x - 1 := by nlinarith
  have hR : 0 ≤ a * b * (2 * x + 1) := by positivity
  have hkey : 2 * x ^ 2 + 2 * x - 1 ≤ a * b * (2 * x + 1) := by
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hL, abs_of_nonneg hR] at h
  have h4 : 4 * a ^ 2 * b ^ 2 = 4 * (x * (x + 1)) := by
    have e : a ^ 2 * b ^ 2 = (a * b) ^ 2 := by rw [mul_pow]
    calc 4 * a ^ 2 * b ^ 2 = 4 * (a ^ 2 * b ^ 2) := by ring
      _ = 4 * (a * b) ^ 2 := by rw [e]
      _ = 4 * (x * (x + 1)) := by rw [hp2]
  have hgoal2 : (a ^ 3 + b ^ 3) * (b + a) = x ^ 2 + (x + 1) ^ 2 + (a * b) * (a ^ 2 + b ^ 2) := by
    rw [← hbb, ← haa]
    ring
  have hgoal3 : x ^ 2 + (x + 1) ^ 2 + (a * b) * (a ^ 2 + b ^ 2) =
      x ^ 2 + (x + 1) ^ 2 + (a * b) * (2 * x + 1) := by
    rw [haa, hbb]
    ring
  have hfinal : 4 * a ^ 2 * b ^ 2 * (b - a) ≤ a ^ 3 + b ^ 3 := by
    have h1 : 4 * a ^ 2 * b ^ 2 * (b - a) = 4 * a ^ 2 * b ^ 2 / (b + a) := by
      rw [hba]; ring
    rw [h1, div_le_iff₀ hb1, hgoal2, hgoal3, h4]
    nlinarith [hkey]
  have hTa : (1 / (x * Real.sqrt x) -
      (2 / Real.sqrt x + (1/2)/(x * Real.sqrt x) -
        (2 / Real.sqrt (x + 1) + (1/2)/((x + 1) * Real.sqrt (x + 1))))) *
      (2 * a ^ 3 * b ^ 3) = a ^ 3 + b ^ 3 - 4 * a ^ 2 * b ^ 2 * (b - a) := by
    rw [← hb, ← ha, ← hbb, ← haa]
    field_simp
    ring
  have hpos : 0 < 2 * a ^ 3 * b ^ 3 := by positivity
  nlinarith [hTa, hfinal, hpos]

private lemma trap_step (m : ℕ) (hm : 1 ≤ m) :
    2 / Real.sqrt ((m:ℝ)+1) + (1/2)/(((m:ℝ)+1) * Real.sqrt ((m:ℝ)+1)) -
        (2 / Real.sqrt (((m+1:ℕ):ℝ)+1) +
          (1/2)/((((m+1:ℕ):ℝ)+1) * Real.sqrt (((m+1:ℕ):ℝ)+1))) ≤
      1 / (((m:ℝ)+1) * Real.sqrt ((m:ℝ)+1)) := by
  have hcast : (((m+1:ℕ):ℝ)+1) = (m:ℝ)+2 := by norm_num; linarith
  rw [hcast]
  set x := (m:ℝ)+1 with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; norm_num
  have hx2 : (m:ℝ)+2 = x+1 := by rw [hxdef]; norm_num; linarith
  rw [hx2]
  exact trap_real x hx1


private lemma zb_0 :
    (1:ℝ)/((((0:ℕ):ℝ) + 1) * Real.sqrt (((0:ℕ):ℝ) + 1)) ≥ (10000000000:ℝ)/10000000000 := by
  have hq : Real.sqrt (((0:ℕ):ℝ) + 1) ≤ (1000000000:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((0:ℕ):ℝ) + 1) * Real.sqrt (((0:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (10000000000:ℝ)/10000000000 * ((((0:ℕ):ℝ) + 1) * ((1000000000:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_1 :
    (1:ℝ)/((((1:ℕ):ℝ) + 1) * Real.sqrt (((1:ℕ):ℝ) + 1)) ≥ (3535533904:ℝ)/10000000000 := by
  have hq : Real.sqrt (((1:ℕ):ℝ) + 1) ≤ (1414213563:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((1:ℕ):ℝ) + 1) * Real.sqrt (((1:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (3535533904:ℝ)/10000000000 * ((((1:ℕ):ℝ) + 1) * ((1414213563:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_2 :
    (1:ℝ)/((((2:ℕ):ℝ) + 1) * Real.sqrt (((2:ℕ):ℝ) + 1)) ≥ (1924500896:ℝ)/10000000000 := by
  have hq : Real.sqrt (((2:ℕ):ℝ) + 1) ≤ (1732050808:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((2:ℕ):ℝ) + 1) * Real.sqrt (((2:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (1924500896:ℝ)/10000000000 * ((((2:ℕ):ℝ) + 1) * ((1732050808:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_3 :
    (1:ℝ)/((((3:ℕ):ℝ) + 1) * Real.sqrt (((3:ℕ):ℝ) + 1)) ≥ (1250000000:ℝ)/10000000000 := by
  have hq : Real.sqrt (((3:ℕ):ℝ) + 1) ≤ (2000000000:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((3:ℕ):ℝ) + 1) * Real.sqrt (((3:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (1250000000:ℝ)/10000000000 * ((((3:ℕ):ℝ) + 1) * ((2000000000:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_4 :
    (1:ℝ)/((((4:ℕ):ℝ) + 1) * Real.sqrt (((4:ℕ):ℝ) + 1)) ≥ (894427190:ℝ)/10000000000 := by
  have hq : Real.sqrt (((4:ℕ):ℝ) + 1) ≤ (2236067978:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((4:ℕ):ℝ) + 1) * Real.sqrt (((4:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (894427190:ℝ)/10000000000 * ((((4:ℕ):ℝ) + 1) * ((2236067978:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_5 :
    (1:ℝ)/((((5:ℕ):ℝ) + 1) * Real.sqrt (((5:ℕ):ℝ) + 1)) ≥ (680413817:ℝ)/10000000000 := by
  have hq : Real.sqrt (((5:ℕ):ℝ) + 1) ≤ (2449489743:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((5:ℕ):ℝ) + 1) * Real.sqrt (((5:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (680413817:ℝ)/10000000000 * ((((5:ℕ):ℝ) + 1) * ((2449489743:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_6 :
    (1:ℝ)/((((6:ℕ):ℝ) + 1) * Real.sqrt (((6:ℕ):ℝ) + 1)) ≥ (539949246:ℝ)/10000000000 := by
  have hq : Real.sqrt (((6:ℕ):ℝ) + 1) ≤ (2645751312:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((6:ℕ):ℝ) + 1) * Real.sqrt (((6:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (539949246:ℝ)/10000000000 * ((((6:ℕ):ℝ) + 1) * ((2645751312:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_7 :
    (1:ℝ)/((((7:ℕ):ℝ) + 1) * Real.sqrt (((7:ℕ):ℝ) + 1)) ≥ (441941738:ℝ)/10000000000 := by
  have hq : Real.sqrt (((7:ℕ):ℝ) + 1) ≤ (2828427125:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((7:ℕ):ℝ) + 1) * Real.sqrt (((7:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (441941738:ℝ)/10000000000 * ((((7:ℕ):ℝ) + 1) * ((2828427125:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_8 :
    (1:ℝ)/((((8:ℕ):ℝ) + 1) * Real.sqrt (((8:ℕ):ℝ) + 1)) ≥ (370370370:ℝ)/10000000000 := by
  have hq : Real.sqrt (((8:ℕ):ℝ) + 1) ≤ (3000000000:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((8:ℕ):ℝ) + 1) * Real.sqrt (((8:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (370370370:ℝ)/10000000000 * ((((8:ℕ):ℝ) + 1) * ((3000000000:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_9 :
    (1:ℝ)/((((9:ℕ):ℝ) + 1) * Real.sqrt (((9:ℕ):ℝ) + 1)) ≥ (316227765:ℝ)/10000000000 := by
  have hq : Real.sqrt (((9:ℕ):ℝ) + 1) ≤ (3162277661:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((9:ℕ):ℝ) + 1) * Real.sqrt (((9:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (316227765:ℝ)/10000000000 * ((((9:ℕ):ℝ) + 1) * ((3162277661:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_10 :
    (1:ℝ)/((((10:ℕ):ℝ) + 1) * Real.sqrt (((10:ℕ):ℝ) + 1)) ≥ (274101222:ℝ)/10000000000 := by
  have hq : Real.sqrt (((10:ℕ):ℝ) + 1) ≤ (3316624791:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((10:ℕ):ℝ) + 1) * Real.sqrt (((10:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (274101222:ℝ)/10000000000 * ((((10:ℕ):ℝ) + 1) * ((3316624791:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_11 :
    (1:ℝ)/((((11:ℕ):ℝ) + 1) * Real.sqrt (((11:ℕ):ℝ) + 1)) ≥ (240562612:ℝ)/10000000000 := by
  have hq : Real.sqrt (((11:ℕ):ℝ) + 1) ≤ (3464101616:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((11:ℕ):ℝ) + 1) * Real.sqrt (((11:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (240562612:ℝ)/10000000000 * ((((11:ℕ):ℝ) + 1) * ((3464101616:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_12 :
    (1:ℝ)/((((12:ℕ):ℝ) + 1) * Real.sqrt (((12:ℕ):ℝ) + 1)) ≥ (213346229:ℝ)/10000000000 := by
  have hq : Real.sqrt (((12:ℕ):ℝ) + 1) ≤ (3605551276:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((12:ℕ):ℝ) + 1) * Real.sqrt (((12:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (213346229:ℝ)/10000000000 * ((((12:ℕ):ℝ) + 1) * ((3605551276:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_13 :
    (1:ℝ)/((((13:ℕ):ℝ) + 1) * Real.sqrt (((13:ℕ):ℝ) + 1)) ≥ (190900887:ℝ)/10000000000 := by
  have hq : Real.sqrt (((13:ℕ):ℝ) + 1) ≤ (3741657387:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((13:ℕ):ℝ) + 1) * Real.sqrt (((13:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (190900887:ℝ)/10000000000 * ((((13:ℕ):ℝ) + 1) * ((3741657387:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_14 :
    (1:ℝ)/((((14:ℕ):ℝ) + 1) * Real.sqrt (((14:ℕ):ℝ) + 1)) ≥ (172132593:ℝ)/10000000000 := by
  have hq : Real.sqrt (((14:ℕ):ℝ) + 1) ≤ (3872983347:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((14:ℕ):ℝ) + 1) * Real.sqrt (((14:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (172132593:ℝ)/10000000000 * ((((14:ℕ):ℝ) + 1) * ((3872983347:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_15 :
    (1:ℝ)/((((15:ℕ):ℝ) + 1) * Real.sqrt (((15:ℕ):ℝ) + 1)) ≥ (156250000:ℝ)/10000000000 := by
  have hq : Real.sqrt (((15:ℕ):ℝ) + 1) ≤ (4000000000:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((15:ℕ):ℝ) + 1) * Real.sqrt (((15:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (156250000:ℝ)/10000000000 * ((((15:ℕ):ℝ) + 1) * ((4000000000:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_16 :
    (1:ℝ)/((((16:ℕ):ℝ) + 1) * Real.sqrt (((16:ℕ):ℝ) + 1)) ≥ (142668014:ℝ)/10000000000 := by
  have hq : Real.sqrt (((16:ℕ):ℝ) + 1) ≤ (4123105626:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((16:ℕ):ℝ) + 1) * Real.sqrt (((16:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (142668014:ℝ)/10000000000 * ((((16:ℕ):ℝ) + 1) * ((4123105626:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_17 :
    (1:ℝ)/((((17:ℕ):ℝ) + 1) * Real.sqrt (((17:ℕ):ℝ) + 1)) ≥ (130945700:ℝ)/10000000000 := by
  have hq : Real.sqrt (((17:ℕ):ℝ) + 1) ≤ (4242640688:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((17:ℕ):ℝ) + 1) * Real.sqrt (((17:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (130945700:ℝ)/10000000000 * ((((17:ℕ):ℝ) + 1) * ((4242640688:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_18 :
    (1:ℝ)/((((18:ℕ):ℝ) + 1) * Real.sqrt (((18:ℕ):ℝ) + 1)) ≥ (120745123:ℝ)/10000000000 := by
  have hq : Real.sqrt (((18:ℕ):ℝ) + 1) ≤ (4358898944:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((18:ℕ):ℝ) + 1) * Real.sqrt (((18:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (120745123:ℝ)/10000000000 * ((((18:ℕ):ℝ) + 1) * ((4358898944:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_19 :
    (1:ℝ)/((((19:ℕ):ℝ) + 1) * Real.sqrt (((19:ℕ):ℝ) + 1)) ≥ (111803398:ℝ)/10000000000 := by
  have hq : Real.sqrt (((19:ℕ):ℝ) + 1) ≤ (4472135955:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((19:ℕ):ℝ) + 1) * Real.sqrt (((19:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (111803398:ℝ)/10000000000 * ((((19:ℕ):ℝ) + 1) * ((4472135955:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_20 :
    (1:ℝ)/((((20:ℕ):ℝ) + 1) * Real.sqrt (((20:ℕ):ℝ) + 1)) ≥ (103913281:ℝ)/10000000000 := by
  have hq : Real.sqrt (((20:ℕ):ℝ) + 1) ≤ (4582575695:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((20:ℕ):ℝ) + 1) * Real.sqrt (((20:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (103913281:ℝ)/10000000000 * ((((20:ℕ):ℝ) + 1) * ((4582575695:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_21 :
    (1:ℝ)/((((21:ℕ):ℝ) + 1) * Real.sqrt (((21:ℕ):ℝ) + 1)) ≥ (96909416:ℝ)/10000000000 := by
  have hq : Real.sqrt (((21:ℕ):ℝ) + 1) ≤ (4690415760:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((21:ℕ):ℝ) + 1) * Real.sqrt (((21:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (96909416:ℝ)/10000000000 * ((((21:ℕ):ℝ) + 1) * ((4690415760:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_22 :
    (1:ℝ)/((((22:ℕ):ℝ) + 1) * Real.sqrt (((22:ℕ):ℝ) + 1)) ≥ (90658440:ℝ)/10000000000 := by
  have hq : Real.sqrt (((22:ℕ):ℝ) + 1) ≤ (4795831524:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((22:ℕ):ℝ) + 1) * Real.sqrt (((22:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (90658440:ℝ)/10000000000 * ((((22:ℕ):ℝ) + 1) * ((4795831524:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_23 :
    (1:ℝ)/((((23:ℕ):ℝ) + 1) * Real.sqrt (((23:ℕ):ℝ) + 1)) ≥ (85051727:ℝ)/10000000000 := by
  have hq : Real.sqrt (((23:ℕ):ℝ) + 1) ≤ (4898979486:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((23:ℕ):ℝ) + 1) * Real.sqrt (((23:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (85051727:ℝ)/10000000000 * ((((23:ℕ):ℝ) + 1) * ((4898979486:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_24 :
    (1:ℝ)/((((24:ℕ):ℝ) + 1) * Real.sqrt (((24:ℕ):ℝ) + 1)) ≥ (80000000:ℝ)/10000000000 := by
  have hq : Real.sqrt (((24:ℕ):ℝ) + 1) ≤ (5000000000:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((24:ℕ):ℝ) + 1) * Real.sqrt (((24:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (80000000:ℝ)/10000000000 * ((((24:ℕ):ℝ) + 1) * ((5000000000:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_25 :
    (1:ℝ)/((((25:ℕ):ℝ) + 1) * Real.sqrt (((25:ℕ):ℝ) + 1)) ≥ (75429282:ℝ)/10000000000 := by
  have hq : Real.sqrt (((25:ℕ):ℝ) + 1) ≤ (5099019514:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((25:ℕ):ℝ) + 1) * Real.sqrt (((25:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (75429282:ℝ)/10000000000 * ((((25:ℕ):ℝ) + 1) * ((5099019514:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_26 :
    (1:ℝ)/((((26:ℕ):ℝ) + 1) * Real.sqrt (((26:ℕ):ℝ) + 1)) ≥ (71277811:ℝ)/10000000000 := by
  have hq : Real.sqrt (((26:ℕ):ℝ) + 1) ≤ (5196152423:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((26:ℕ):ℝ) + 1) * Real.sqrt (((26:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (71277811:ℝ)/10000000000 * ((((26:ℕ):ℝ) + 1) * ((5196152423:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_27 :
    (1:ℝ)/((((27:ℕ):ℝ) + 1) * Real.sqrt (((27:ℕ):ℝ) + 1)) ≥ (67493655:ℝ)/10000000000 := by
  have hq : Real.sqrt (((27:ℕ):ℝ) + 1) ≤ (5291502623:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((27:ℕ):ℝ) + 1) * Real.sqrt (((27:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (67493655:ℝ)/10000000000 * ((((27:ℕ):ℝ) + 1) * ((5291502623:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_28 :
    (1:ℝ)/((((28:ℕ):ℝ) + 1) * Real.sqrt (((28:ℕ):ℝ) + 1)) ≥ (64032875:ℝ)/10000000000 := by
  have hq : Real.sqrt (((28:ℕ):ℝ) + 1) ≤ (5385164808:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((28:ℕ):ℝ) + 1) * Real.sqrt (((28:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (64032875:ℝ)/10000000000 * ((((28:ℕ):ℝ) + 1) * ((5385164808:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_29 :
    (1:ℝ)/((((29:ℕ):ℝ) + 1) * Real.sqrt (((29:ℕ):ℝ) + 1)) ≥ (60858061:ℝ)/10000000000 := by
  have hq : Real.sqrt (((29:ℕ):ℝ) + 1) ≤ (5477225576:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((29:ℕ):ℝ) + 1) * Real.sqrt (((29:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (60858061:ℝ)/10000000000 * ((((29:ℕ):ℝ) + 1) * ((5477225576:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_30 :
    (1:ℝ)/((((30:ℕ):ℝ) + 1) * Real.sqrt (((30:ℕ):ℝ) + 1)) ≥ (57937194:ℝ)/10000000000 := by
  have hq : Real.sqrt (((30:ℕ):ℝ) + 1) ≤ (5567764363:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((30:ℕ):ℝ) + 1) * Real.sqrt (((30:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (57937194:ℝ)/10000000000 * ((((30:ℕ):ℝ) + 1) * ((5567764363:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_31 :
    (1:ℝ)/((((31:ℕ):ℝ) + 1) * Real.sqrt (((31:ℕ):ℝ) + 1)) ≥ (55242717:ℝ)/10000000000 := by
  have hq : Real.sqrt (((31:ℕ):ℝ) + 1) ≤ (5656854250:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((31:ℕ):ℝ) + 1) * Real.sqrt (((31:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (55242717:ℝ)/10000000000 * ((((31:ℕ):ℝ) + 1) * ((5656854250:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_32 :
    (1:ℝ)/((((32:ℕ):ℝ) + 1) * Real.sqrt (((32:ℕ):ℝ) + 1)) ≥ (52750804:ℝ)/10000000000 := by
  have hq : Real.sqrt (((32:ℕ):ℝ) + 1) ≤ (5744562647:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((32:ℕ):ℝ) + 1) * Real.sqrt (((32:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (52750804:ℝ)/10000000000 * ((((32:ℕ):ℝ) + 1) * ((5744562647:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_33 :
    (1:ℝ)/((((33:ℕ):ℝ) + 1) * Real.sqrt (((33:ℕ):ℝ) + 1)) ≥ (50440760:ℝ)/10000000000 := by
  have hq : Real.sqrt (((33:ℕ):ℝ) + 1) ≤ (5830951895:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((33:ℕ):ℝ) + 1) * Real.sqrt (((33:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (50440760:ℝ)/10000000000 * ((((33:ℕ):ℝ) + 1) * ((5830951895:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_34 :
    (1:ℝ)/((((34:ℕ):ℝ) + 1) * Real.sqrt (((34:ℕ):ℝ) + 1)) ≥ (48294528:ℝ)/10000000000 := by
  have hq : Real.sqrt (((34:ℕ):ℝ) + 1) ≤ (5916079784:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((34:ℕ):ℝ) + 1) * Real.sqrt (((34:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (48294528:ℝ)/10000000000 * ((((34:ℕ):ℝ) + 1) * ((5916079784:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_35 :
    (1:ℝ)/((((35:ℕ):ℝ) + 1) * Real.sqrt (((35:ℕ):ℝ) + 1)) ≥ (46296296:ℝ)/10000000000 := by
  have hq : Real.sqrt (((35:ℕ):ℝ) + 1) ≤ (6000000000:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((35:ℕ):ℝ) + 1) * Real.sqrt (((35:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (46296296:ℝ)/10000000000 * ((((35:ℕ):ℝ) + 1) * ((6000000000:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_36 :
    (1:ℝ)/((((36:ℕ):ℝ) + 1) * Real.sqrt (((36:ℕ):ℝ) + 1)) ≥ (44432158:ℝ)/10000000000 := by
  have hq : Real.sqrt (((36:ℕ):ℝ) + 1) ≤ (6082762531:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((36:ℕ):ℝ) + 1) * Real.sqrt (((36:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (44432158:ℝ)/10000000000 * ((((36:ℕ):ℝ) + 1) * ((6082762531:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_37 :
    (1:ℝ)/((((37:ℕ):ℝ) + 1) * Real.sqrt (((37:ℕ):ℝ) + 1)) ≥ (42689847:ℝ)/10000000000 := by
  have hq : Real.sqrt (((37:ℕ):ℝ) + 1) ≤ (6164414003:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((37:ℕ):ℝ) + 1) * Real.sqrt (((37:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (42689847:ℝ)/10000000000 * ((((37:ℕ):ℝ) + 1) * ((6164414003:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_38 :
    (1:ℝ)/((((38:ℕ):ℝ) + 1) * Real.sqrt (((38:ℕ):ℝ) + 1)) ≥ (41058500:ℝ)/10000000000 := by
  have hq : Real.sqrt (((38:ℕ):ℝ) + 1) ≤ (6244997999:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((38:ℕ):ℝ) + 1) * Real.sqrt (((38:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (41058500:ℝ)/10000000000 * ((((38:ℕ):ℝ) + 1) * ((6244997999:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_39 :
    (1:ℝ)/((((39:ℕ):ℝ) + 1) * Real.sqrt (((39:ℕ):ℝ) + 1)) ≥ (39528470:ℝ)/10000000000 := by
  have hq : Real.sqrt (((39:ℕ):ℝ) + 1) ≤ (6324555321:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((39:ℕ):ℝ) + 1) * Real.sqrt (((39:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (39528470:ℝ)/10000000000 * ((((39:ℕ):ℝ) + 1) * ((6324555321:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_40 :
    (1:ℝ)/((((40:ℕ):ℝ) + 1) * Real.sqrt (((40:ℕ):ℝ) + 1)) ≥ (38091161:ℝ)/10000000000 := by
  have hq : Real.sqrt (((40:ℕ):ℝ) + 1) ≤ (6403124238:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((40:ℕ):ℝ) + 1) * Real.sqrt (((40:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (38091161:ℝ)/10000000000 * ((((40:ℕ):ℝ) + 1) * ((6403124238:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_41 :
    (1:ℝ)/((((41:ℕ):ℝ) + 1) * Real.sqrt (((41:ℕ):ℝ) + 1)) ≥ (36738892:ℝ)/10000000000 := by
  have hq : Real.sqrt (((41:ℕ):ℝ) + 1) ≤ (6480740699:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((41:ℕ):ℝ) + 1) * Real.sqrt (((41:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (36738892:ℝ)/10000000000 * ((((41:ℕ):ℝ) + 1) * ((6480740699:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_42 :
    (1:ℝ)/((((42:ℕ):ℝ) + 1) * Real.sqrt (((42:ℕ):ℝ) + 1)) ≥ (35464783:ℝ)/10000000000 := by
  have hq : Real.sqrt (((42:ℕ):ℝ) + 1) ≤ (6557438525:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((42:ℕ):ℝ) + 1) * Real.sqrt (((42:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (35464783:ℝ)/10000000000 * ((((42:ℕ):ℝ) + 1) * ((6557438525:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_43 :
    (1:ℝ)/((((43:ℕ):ℝ) + 1) * Real.sqrt (((43:ℕ):ℝ) + 1)) ≥ (34262652:ℝ)/10000000000 := by
  have hq : Real.sqrt (((43:ℕ):ℝ) + 1) ≤ (6633249581:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((43:ℕ):ℝ) + 1) * Real.sqrt (((43:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (34262652:ℝ)/10000000000 * ((((43:ℕ):ℝ) + 1) * ((6633249581:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_44 :
    (1:ℝ)/((((44:ℕ):ℝ) + 1) * Real.sqrt (((44:ℕ):ℝ) + 1)) ≥ (33126932:ℝ)/10000000000 := by
  have hq : Real.sqrt (((44:ℕ):ℝ) + 1) ≤ (6708203933:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((44:ℕ):ℝ) + 1) * Real.sqrt (((44:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (33126932:ℝ)/10000000000 * ((((44:ℕ):ℝ) + 1) * ((6708203933:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_45 :
    (1:ℝ)/((((45:ℕ):ℝ) + 1) * Real.sqrt (((45:ℕ):ℝ) + 1)) ≥ (32052599:ℝ)/10000000000 := by
  have hq : Real.sqrt (((45:ℕ):ℝ) + 1) ≤ (6782329984:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((45:ℕ):ℝ) + 1) * Real.sqrt (((45:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (32052599:ℝ)/10000000000 * ((((45:ℕ):ℝ) + 1) * ((6782329984:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_46 :
    (1:ℝ)/((((46:ℕ):ℝ) + 1) * Real.sqrt (((46:ℕ):ℝ) + 1)) ≥ (31035104:ℝ)/10000000000 := by
  have hq : Real.sqrt (((46:ℕ):ℝ) + 1) ≤ (6855654601:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((46:ℕ):ℝ) + 1) * Real.sqrt (((46:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (31035104:ℝ)/10000000000 * ((((46:ℕ):ℝ) + 1) * ((6855654601:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_47 :
    (1:ℝ)/((((47:ℕ):ℝ) + 1) * Real.sqrt (((47:ℕ):ℝ) + 1)) ≥ (30070326:ℝ)/10000000000 := by
  have hq : Real.sqrt (((47:ℕ):ℝ) + 1) ≤ (6928203231:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((47:ℕ):ℝ) + 1) * Real.sqrt (((47:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (30070326:ℝ)/10000000000 * ((((47:ℕ):ℝ) + 1) * ((6928203231:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_48 :
    (1:ℝ)/((((48:ℕ):ℝ) + 1) * Real.sqrt (((48:ℕ):ℝ) + 1)) ≥ (29154518:ℝ)/10000000000 := by
  have hq : Real.sqrt (((48:ℕ):ℝ) + 1) ≤ (7000000000:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((48:ℕ):ℝ) + 1) * Real.sqrt (((48:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (29154518:ℝ)/10000000000 * ((((48:ℕ):ℝ) + 1) * ((7000000000:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_49 :
    (1:ℝ)/((((49:ℕ):ℝ) + 1) * Real.sqrt (((49:ℕ):ℝ) + 1)) ≥ (28284271:ℝ)/10000000000 := by
  have hq : Real.sqrt (((49:ℕ):ℝ) + 1) ≤ (7071067812:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((49:ℕ):ℝ) + 1) * Real.sqrt (((49:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (28284271:ℝ)/10000000000 * ((((49:ℕ):ℝ) + 1) * ((7071067812:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_50 :
    (1:ℝ)/((((50:ℕ):ℝ) + 1) * Real.sqrt (((50:ℕ):ℝ) + 1)) ≥ (27456472:ℝ)/10000000000 := by
  have hq : Real.sqrt (((50:ℕ):ℝ) + 1) ≤ (7141428429:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((50:ℕ):ℝ) + 1) * Real.sqrt (((50:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (27456472:ℝ)/10000000000 * ((((50:ℕ):ℝ) + 1) * ((7141428429:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_51 :
    (1:ℝ)/((((51:ℕ):ℝ) + 1) * Real.sqrt (((51:ℕ):ℝ) + 1)) ≥ (26668278:ℝ)/10000000000 := by
  have hq : Real.sqrt (((51:ℕ):ℝ) + 1) ≤ (7211102551:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((51:ℕ):ℝ) + 1) * Real.sqrt (((51:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (26668278:ℝ)/10000000000 * ((((51:ℕ):ℝ) + 1) * ((7211102551:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_52 :
    (1:ℝ)/((((52:ℕ):ℝ) + 1) * Real.sqrt (((52:ℕ):ℝ) + 1)) ≥ (25917087:ℝ)/10000000000 := by
  have hq : Real.sqrt (((52:ℕ):ℝ) + 1) ≤ (7280109890:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((52:ℕ):ℝ) + 1) * Real.sqrt (((52:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (25917087:ℝ)/10000000000 * ((((52:ℕ):ℝ) + 1) * ((7280109890:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_53 :
    (1:ℝ)/((((53:ℕ):ℝ) + 1) * Real.sqrt (((53:ℕ):ℝ) + 1)) ≥ (25200511:ℝ)/10000000000 := by
  have hq : Real.sqrt (((53:ℕ):ℝ) + 1) ≤ (7348469229:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((53:ℕ):ℝ) + 1) * Real.sqrt (((53:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (25200511:ℝ)/10000000000 * ((((53:ℕ):ℝ) + 1) * ((7348469229:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_54 :
    (1:ℝ)/((((54:ℕ):ℝ) + 1) * Real.sqrt (((54:ℕ):ℝ) + 1)) ≥ (24516358:ℝ)/10000000000 := by
  have hq : Real.sqrt (((54:ℕ):ℝ) + 1) ≤ (7416198488:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((54:ℕ):ℝ) + 1) * Real.sqrt (((54:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (24516358:ℝ)/10000000000 * ((((54:ℕ):ℝ) + 1) * ((7416198488:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_55 :
    (1:ℝ)/((((55:ℕ):ℝ) + 1) * Real.sqrt (((55:ℕ):ℝ) + 1)) ≥ (23862610:ℝ)/10000000000 := by
  have hq : Real.sqrt (((55:ℕ):ℝ) + 1) ≤ (7483314774:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((55:ℕ):ℝ) + 1) * Real.sqrt (((55:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (23862610:ℝ)/10000000000 * ((((55:ℕ):ℝ) + 1) * ((7483314774:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_56 :
    (1:ℝ)/((((56:ℕ):ℝ) + 1) * Real.sqrt (((56:ℕ):ℝ) + 1)) ≥ (23237409:ℝ)/10000000000 := by
  have hq : Real.sqrt (((56:ℕ):ℝ) + 1) ≤ (7549834436:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((56:ℕ):ℝ) + 1) * Real.sqrt (((56:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (23237409:ℝ)/10000000000 * ((((56:ℕ):ℝ) + 1) * ((7549834436:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_57 :
    (1:ℝ)/((((57:ℕ):ℝ) + 1) * Real.sqrt (((57:ℕ):ℝ) + 1)) ≥ (22639040:ℝ)/10000000000 := by
  have hq : Real.sqrt (((57:ℕ):ℝ) + 1) ≤ (7615773106:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((57:ℕ):ℝ) + 1) * Real.sqrt (((57:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (22639040:ℝ)/10000000000 * ((((57:ℕ):ℝ) + 1) * ((7615773106:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_58 :
    (1:ℝ)/((((58:ℕ):ℝ) + 1) * Real.sqrt (((58:ℕ):ℝ) + 1)) ≥ (22065917:ℝ)/10000000000 := by
  have hq : Real.sqrt (((58:ℕ):ℝ) + 1) ≤ (7681145748:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((58:ℕ):ℝ) + 1) * Real.sqrt (((58:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (22065917:ℝ)/10000000000 * ((((58:ℕ):ℝ) + 1) * ((7681145748:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_59 :
    (1:ℝ)/((((59:ℕ):ℝ) + 1) * Real.sqrt (((59:ℕ):ℝ) + 1)) ≥ (21516574:ℝ)/10000000000 := by
  have hq : Real.sqrt (((59:ℕ):ℝ) + 1) ≤ (7745966693:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((59:ℕ):ℝ) + 1) * Real.sqrt (((59:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (21516574:ℝ)/10000000000 * ((((59:ℕ):ℝ) + 1) * ((7745966693:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_60 :
    (1:ℝ)/((((60:ℕ):ℝ) + 1) * Real.sqrt (((60:ℕ):ℝ) + 1)) ≥ (20989652:ℝ)/10000000000 := by
  have hq : Real.sqrt (((60:ℕ):ℝ) + 1) ≤ (7810249676:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((60:ℕ):ℝ) + 1) * Real.sqrt (((60:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (20989652:ℝ)/10000000000 * ((((60:ℕ):ℝ) + 1) * ((7810249676:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_61 :
    (1:ℝ)/((((61:ℕ):ℝ) + 1) * Real.sqrt (((61:ℕ):ℝ) + 1)) ≥ (20483891:ℝ)/10000000000 := by
  have hq : Real.sqrt (((61:ℕ):ℝ) + 1) ≤ (7874007875:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((61:ℕ):ℝ) + 1) * Real.sqrt (((61:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (20483891:ℝ)/10000000000 * ((((61:ℕ):ℝ) + 1) * ((7874007875:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_62 :
    (1:ℝ)/((((62:ℕ):ℝ) + 1) * Real.sqrt (((62:ℕ):ℝ) + 1)) ≥ (19998120:ℝ)/10000000000 := by
  have hq : Real.sqrt (((62:ℕ):ℝ) + 1) ≤ (7937253934:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((62:ℕ):ℝ) + 1) * Real.sqrt (((62:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (19998120:ℝ)/10000000000 * ((((62:ℕ):ℝ) + 1) * ((7937253934:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_63 :
    (1:ℝ)/((((63:ℕ):ℝ) + 1) * Real.sqrt (((63:ℕ):ℝ) + 1)) ≥ (19531250:ℝ)/10000000000 := by
  have hq : Real.sqrt (((63:ℕ):ℝ) + 1) ≤ (8000000000:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((63:ℕ):ℝ) + 1) * Real.sqrt (((63:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (19531250:ℝ)/10000000000 * ((((63:ℕ):ℝ) + 1) * ((8000000000:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_64 :
    (1:ℝ)/((((64:ℕ):ℝ) + 1) * Real.sqrt (((64:ℕ):ℝ) + 1)) ≥ (19082266:ℝ)/10000000000 := by
  have hq : Real.sqrt (((64:ℕ):ℝ) + 1) ≤ (8062257749:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((64:ℕ):ℝ) + 1) * Real.sqrt (((64:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (19082266:ℝ)/10000000000 * ((((64:ℕ):ℝ) + 1) * ((8062257749:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_65 :
    (1:ℝ)/((((65:ℕ):ℝ) + 1) * Real.sqrt (((65:ℕ):ℝ) + 1)) ≥ (18650225:ℝ)/10000000000 := by
  have hq : Real.sqrt (((65:ℕ):ℝ) + 1) ≤ (8124038405:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((65:ℕ):ℝ) + 1) * Real.sqrt (((65:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (18650225:ℝ)/10000000000 * ((((65:ℕ):ℝ) + 1) * ((8124038405:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_66 :
    (1:ℝ)/((((66:ℕ):ℝ) + 1) * Real.sqrt (((66:ℕ):ℝ) + 1)) ≥ (18234245:ℝ)/10000000000 := by
  have hq : Real.sqrt (((66:ℕ):ℝ) + 1) ≤ (8185352772:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((66:ℕ):ℝ) + 1) * Real.sqrt (((66:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (18234245:ℝ)/10000000000 * ((((66:ℕ):ℝ) + 1) * ((8185352772:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_67 :
    (1:ℝ)/((((67:ℕ):ℝ) + 1) * Real.sqrt (((67:ℕ):ℝ) + 1)) ≥ (17833501:ℝ)/10000000000 := by
  have hq : Real.sqrt (((67:ℕ):ℝ) + 1) ≤ (8246211252:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((67:ℕ):ℝ) + 1) * Real.sqrt (((67:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (17833501:ℝ)/10000000000 * ((((67:ℕ):ℝ) + 1) * ((8246211252:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_68 :
    (1:ℝ)/((((68:ℕ):ℝ) + 1) * Real.sqrt (((68:ℕ):ℝ) + 1)) ≥ (17447225:ℝ)/10000000000 := by
  have hq : Real.sqrt (((68:ℕ):ℝ) + 1) ≤ (8306623863:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((68:ℕ):ℝ) + 1) * Real.sqrt (((68:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (17447225:ℝ)/10000000000 * ((((68:ℕ):ℝ) + 1) * ((8306623863:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_69 :
    (1:ℝ)/((((69:ℕ):ℝ) + 1) * Real.sqrt (((69:ℕ):ℝ) + 1)) ≥ (17074694:ℝ)/10000000000 := by
  have hq : Real.sqrt (((69:ℕ):ℝ) + 1) ≤ (8366600266:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((69:ℕ):ℝ) + 1) * Real.sqrt (((69:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (17074694:ℝ)/10000000000 * ((((69:ℕ):ℝ) + 1) * ((8366600266:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_70 :
    (1:ℝ)/((((70:ℕ):ℝ) + 1) * Real.sqrt (((70:ℕ):ℝ) + 1)) ≥ (16715234:ℝ)/10000000000 := by
  have hq : Real.sqrt (((70:ℕ):ℝ) + 1) ≤ (8426149774:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((70:ℕ):ℝ) + 1) * Real.sqrt (((70:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (16715234:ℝ)/10000000000 * ((((70:ℕ):ℝ) + 1) * ((8426149774:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_71 :
    (1:ℝ)/((((71:ℕ):ℝ) + 1) * Real.sqrt (((71:ℕ):ℝ) + 1)) ≥ (16368212:ℝ)/10000000000 := by
  have hq : Real.sqrt (((71:ℕ):ℝ) + 1) ≤ (8485281375:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((71:ℕ):ℝ) + 1) * Real.sqrt (((71:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (16368212:ℝ)/10000000000 * ((((71:ℕ):ℝ) + 1) * ((8485281375:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_72 :
    (1:ℝ)/((((72:ℕ):ℝ) + 1) * Real.sqrt (((72:ℕ):ℝ) + 1)) ≥ (16033033:ℝ)/10000000000 := by
  have hq : Real.sqrt (((72:ℕ):ℝ) + 1) ≤ (8544003746:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((72:ℕ):ℝ) + 1) * Real.sqrt (((72:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (16033033:ℝ)/10000000000 * ((((72:ℕ):ℝ) + 1) * ((8544003746:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_73 :
    (1:ℝ)/((((73:ℕ):ℝ) + 1) * Real.sqrt (((73:ℕ):ℝ) + 1)) ≥ (15709140:ℝ)/10000000000 := by
  have hq : Real.sqrt (((73:ℕ):ℝ) + 1) ≤ (8602325268:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((73:ℕ):ℝ) + 1) * Real.sqrt (((73:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (15709140:ℝ)/10000000000 * ((((73:ℕ):ℝ) + 1) * ((8602325268:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_74 :
    (1:ℝ)/((((74:ℕ):ℝ) + 1) * Real.sqrt (((74:ℕ):ℝ) + 1)) ≥ (15396007:ℝ)/10000000000 := by
  have hq : Real.sqrt (((74:ℕ):ℝ) + 1) ≤ (8660254038:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((74:ℕ):ℝ) + 1) * Real.sqrt (((74:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (15396007:ℝ)/10000000000 * ((((74:ℕ):ℝ) + 1) * ((8660254038:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_75 :
    (1:ℝ)/((((75:ℕ):ℝ) + 1) * Real.sqrt (((75:ℕ):ℝ) + 1)) ≥ (15093140:ℝ)/10000000000 := by
  have hq : Real.sqrt (((75:ℕ):ℝ) + 1) ≤ (8717797888:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((75:ℕ):ℝ) + 1) * Real.sqrt (((75:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (15093140:ℝ)/10000000000 * ((((75:ℕ):ℝ) + 1) * ((8717797888:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_76 :
    (1:ℝ)/((((76:ℕ):ℝ) + 1) * Real.sqrt (((76:ℕ):ℝ) + 1)) ≥ (14800074:ℝ)/10000000000 := by
  have hq : Real.sqrt (((76:ℕ):ℝ) + 1) ≤ (8774964388:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((76:ℕ):ℝ) + 1) * Real.sqrt (((76:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (14800074:ℝ)/10000000000 * ((((76:ℕ):ℝ) + 1) * ((8774964388:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_77 :
    (1:ℝ)/((((77:ℕ):ℝ) + 1) * Real.sqrt (((77:ℕ):ℝ) + 1)) ≥ (14516372:ℝ)/10000000000 := by
  have hq : Real.sqrt (((77:ℕ):ℝ) + 1) ≤ (8831760867:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((77:ℕ):ℝ) + 1) * Real.sqrt (((77:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (14516372:ℝ)/10000000000 * ((((77:ℕ):ℝ) + 1) * ((8831760867:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_78 :
    (1:ℝ)/((((78:ℕ):ℝ) + 1) * Real.sqrt (((78:ℕ):ℝ) + 1)) ≥ (14241618:ℝ)/10000000000 := by
  have hq : Real.sqrt (((78:ℕ):ℝ) + 1) ≤ (8888194418:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((78:ℕ):ℝ) + 1) * Real.sqrt (((78:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (14241618:ℝ)/10000000000 * ((((78:ℕ):ℝ) + 1) * ((8888194418:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_79 :
    (1:ℝ)/((((79:ℕ):ℝ) + 1) * Real.sqrt (((79:ℕ):ℝ) + 1)) ≥ (13975424:ℝ)/10000000000 := by
  have hq : Real.sqrt (((79:ℕ):ℝ) + 1) ≤ (8944271910:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((79:ℕ):ℝ) + 1) * Real.sqrt (((79:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (13975424:ℝ)/10000000000 * ((((79:ℕ):ℝ) + 1) * ((8944271910:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_80 :
    (1:ℝ)/((((80:ℕ):ℝ) + 1) * Real.sqrt (((80:ℕ):ℝ) + 1)) ≥ (13717421:ℝ)/10000000000 := by
  have hq : Real.sqrt (((80:ℕ):ℝ) + 1) ≤ (9000000000:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((80:ℕ):ℝ) + 1) * Real.sqrt (((80:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (13717421:ℝ)/10000000000 * ((((80:ℕ):ℝ) + 1) * ((9000000000:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_81 :
    (1:ℝ)/((((81:ℕ):ℝ) + 1) * Real.sqrt (((81:ℕ):ℝ) + 1)) ≥ (13467259:ℝ)/10000000000 := by
  have hq : Real.sqrt (((81:ℕ):ℝ) + 1) ≤ (9055385139:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((81:ℕ):ℝ) + 1) * Real.sqrt (((81:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (13467259:ℝ)/10000000000 * ((((81:ℕ):ℝ) + 1) * ((9055385139:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_82 :
    (1:ℝ)/((((82:ℕ):ℝ) + 1) * Real.sqrt (((82:ℕ):ℝ) + 1)) ≥ (13224609:ℝ)/10000000000 := by
  have hq : Real.sqrt (((82:ℕ):ℝ) + 1) ≤ (9110433580:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((82:ℕ):ℝ) + 1) * Real.sqrt (((82:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (13224609:ℝ)/10000000000 * ((((82:ℕ):ℝ) + 1) * ((9110433580:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_83 :
    (1:ℝ)/((((83:ℕ):ℝ) + 1) * Real.sqrt (((83:ℕ):ℝ) + 1)) ≥ (12989160:ℝ)/10000000000 := by
  have hq : Real.sqrt (((83:ℕ):ℝ) + 1) ≤ (9165151390:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((83:ℕ):ℝ) + 1) * Real.sqrt (((83:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (12989160:ℝ)/10000000000 * ((((83:ℕ):ℝ) + 1) * ((9165151390:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_84 :
    (1:ℝ)/((((84:ℕ):ℝ) + 1) * Real.sqrt (((84:ℕ):ℝ) + 1)) ≥ (12760615:ℝ)/10000000000 := by
  have hq : Real.sqrt (((84:ℕ):ℝ) + 1) ≤ (9219544458:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((84:ℕ):ℝ) + 1) * Real.sqrt (((84:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (12760615:ℝ)/10000000000 * ((((84:ℕ):ℝ) + 1) * ((9219544458:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_85 :
    (1:ℝ)/((((85:ℕ):ℝ) + 1) * Real.sqrt (((85:ℕ):ℝ) + 1)) ≥ (12538694:ℝ)/10000000000 := by
  have hq : Real.sqrt (((85:ℕ):ℝ) + 1) ≤ (9273618496:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((85:ℕ):ℝ) + 1) * Real.sqrt (((85:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (12538694:ℝ)/10000000000 * ((((85:ℕ):ℝ) + 1) * ((9273618496:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_86 :
    (1:ℝ)/((((86:ℕ):ℝ) + 1) * Real.sqrt (((86:ℕ):ℝ) + 1)) ≥ (12323132:ℝ)/10000000000 := by
  have hq : Real.sqrt (((86:ℕ):ℝ) + 1) ≤ (9327379054:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((86:ℕ):ℝ) + 1) * Real.sqrt (((86:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (12323132:ℝ)/10000000000 * ((((86:ℕ):ℝ) + 1) * ((9327379054:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_87 :
    (1:ℝ)/((((87:ℕ):ℝ) + 1) * Real.sqrt (((87:ℕ):ℝ) + 1)) ≥ (12113677:ℝ)/10000000000 := by
  have hq : Real.sqrt (((87:ℕ):ℝ) + 1) ≤ (9380831520:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((87:ℕ):ℝ) + 1) * Real.sqrt (((87:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (12113677:ℝ)/10000000000 * ((((87:ℕ):ℝ) + 1) * ((9380831520:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_88 :
    (1:ℝ)/((((88:ℕ):ℝ) + 1) * Real.sqrt (((88:ℕ):ℝ) + 1)) ≥ (11910088:ℝ)/10000000000 := by
  have hq : Real.sqrt (((88:ℕ):ℝ) + 1) ≤ (9433981133:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((88:ℕ):ℝ) + 1) * Real.sqrt (((88:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (11910088:ℝ)/10000000000 * ((((88:ℕ):ℝ) + 1) * ((9433981133:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_89 :
    (1:ℝ)/((((89:ℕ):ℝ) + 1) * Real.sqrt (((89:ℕ):ℝ) + 1)) ≥ (11712139:ℝ)/10000000000 := by
  have hq : Real.sqrt (((89:ℕ):ℝ) + 1) ≤ (9486832981:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((89:ℕ):ℝ) + 1) * Real.sqrt (((89:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (11712139:ℝ)/10000000000 * ((((89:ℕ):ℝ) + 1) * ((9486832981:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_90 :
    (1:ℝ)/((((90:ℕ):ℝ) + 1) * Real.sqrt (((90:ℕ):ℝ) + 1)) ≥ (11519613:ℝ)/10000000000 := by
  have hq : Real.sqrt (((90:ℕ):ℝ) + 1) ≤ (9539392015:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((90:ℕ):ℝ) + 1) * Real.sqrt (((90:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (11519613:ℝ)/10000000000 * ((((90:ℕ):ℝ) + 1) * ((9539392015:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_91 :
    (1:ℝ)/((((91:ℕ):ℝ) + 1) * Real.sqrt (((91:ℕ):ℝ) + 1)) ≥ (11332305:ℝ)/10000000000 := by
  have hq : Real.sqrt (((91:ℕ):ℝ) + 1) ≤ (9591663047:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((91:ℕ):ℝ) + 1) * Real.sqrt (((91:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (11332305:ℝ)/10000000000 * ((((91:ℕ):ℝ) + 1) * ((9591663047:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_92 :
    (1:ℝ)/((((92:ℕ):ℝ) + 1) * Real.sqrt (((92:ℕ):ℝ) + 1)) ≥ (11150018:ℝ)/10000000000 := by
  have hq : Real.sqrt (((92:ℕ):ℝ) + 1) ≤ (9643650761:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((92:ℕ):ℝ) + 1) * Real.sqrt (((92:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (11150018:ℝ)/10000000000 * ((((92:ℕ):ℝ) + 1) * ((9643650761:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_93 :
    (1:ℝ)/((((93:ℕ):ℝ) + 1) * Real.sqrt (((93:ℕ):ℝ) + 1)) ≥ (10972566:ℝ)/10000000000 := by
  have hq : Real.sqrt (((93:ℕ):ℝ) + 1) ≤ (9695359715:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((93:ℕ):ℝ) + 1) * Real.sqrt (((93:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (10972566:ℝ)/10000000000 * ((((93:ℕ):ℝ) + 1) * ((9695359715:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_94 :
    (1:ℝ)/((((94:ℕ):ℝ) + 1) * Real.sqrt (((94:ℕ):ℝ) + 1)) ≥ (10799772:ℝ)/10000000000 := by
  have hq : Real.sqrt (((94:ℕ):ℝ) + 1) ≤ (9746794345:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((94:ℕ):ℝ) + 1) * Real.sqrt (((94:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (10799772:ℝ)/10000000000 * ((((94:ℕ):ℝ) + 1) * ((9746794345:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_95 :
    (1:ℝ)/((((95:ℕ):ℝ) + 1) * Real.sqrt (((95:ℕ):ℝ) + 1)) ≥ (10631465:ℝ)/10000000000 := by
  have hq : Real.sqrt (((95:ℕ):ℝ) + 1) ≤ (9797958972:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((95:ℕ):ℝ) + 1) * Real.sqrt (((95:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (10631465:ℝ)/10000000000 * ((((95:ℕ):ℝ) + 1) * ((9797958972:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_96 :
    (1:ℝ)/((((96:ℕ):ℝ) + 1) * Real.sqrt (((96:ℕ):ℝ) + 1)) ≥ (10467486:ℝ)/10000000000 := by
  have hq : Real.sqrt (((96:ℕ):ℝ) + 1) ≤ (9848857802:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((96:ℕ):ℝ) + 1) * Real.sqrt (((96:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (10467486:ℝ)/10000000000 * ((((96:ℕ):ℝ) + 1) * ((9848857802:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_97 :
    (1:ℝ)/((((97:ℕ):ℝ) + 1) * Real.sqrt (((97:ℕ):ℝ) + 1)) ≥ (10307679:ℝ)/10000000000 := by
  have hq : Real.sqrt (((97:ℕ):ℝ) + 1) ≤ (9899494937:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((97:ℕ):ℝ) + 1) * Real.sqrt (((97:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (10307679:ℝ)/10000000000 * ((((97:ℕ):ℝ) + 1) * ((9899494937:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_98 :
    (1:ℝ)/((((98:ℕ):ℝ) + 1) * Real.sqrt (((98:ℕ):ℝ) + 1)) ≥ (10151897:ℝ)/10000000000 := by
  have hq : Real.sqrt (((98:ℕ):ℝ) + 1) ≤ (9949874372:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((98:ℕ):ℝ) + 1) * Real.sqrt (((98:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (10151897:ℝ)/10000000000 * ((((98:ℕ):ℝ) + 1) * ((9949874372:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_99 :
    (1:ℝ)/((((99:ℕ):ℝ) + 1) * Real.sqrt (((99:ℕ):ℝ) + 1)) ≥ (10000000:ℝ)/10000000000 := by
  have hq : Real.sqrt (((99:ℕ):ℝ) + 1) ≤ (10000000000:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((99:ℕ):ℝ) + 1) * Real.sqrt (((99:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (10000000:ℝ)/10000000000 * ((((99:ℕ):ℝ) + 1) * ((10000000000:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]

private lemma zb_100 :
    (1:ℝ)/((((100:ℕ):ℝ) + 1) * Real.sqrt (((100:ℕ):ℝ) + 1)) ≥ (9851853:ℝ)/10000000000 := by
  have hq : Real.sqrt (((100:ℕ):ℝ) + 1) ≤ (10049875622:ℝ)/1000000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : (0:ℝ) < (((100:ℕ):ℝ) + 1) * Real.sqrt (((100:ℕ):ℝ) + 1) := by positivity
  rw [ge_iff_le, le_div_iff₀ hp]
  have h2 : (9851853:ℝ)/10000000000 * ((((100:ℕ):ℝ) + 1) * ((10049875622:ℝ)/1000000000)) ≤ 1 := by
    norm_num
  nlinarith [hq]


/-- LEAF: P0014 page 34, display 4.11, "ζ(3/2) can be evaluated by Euler-Maclaurin":
re ζ(3/2) ≥ 2.61237. The true value is 2.6123753486..., margin 5.3e-6.
Class HARD: a certified Euler-Maclaurin evaluation with explicit remainder. -/
theorem zeta_three_half_ge : (2.61237 : ℝ) ≤ (riemannZeta (3 / 2)).re := by
  set G : ℕ → ℝ := fun n => 2 / Real.sqrt ((n:ℝ)+1) + (1/2)/(((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1)) with hG
  rw [zeta_series]
  rw [← summ.sum_add_tsum_nat_add 101]
  have hexp : (∑ n ∈ Finset.range 101, (1:ℝ)/(((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1))) = 0 + (1:ℝ)/((((0:ℕ):ℝ) + 1) * Real.sqrt (((0:ℕ):ℝ) + 1)) + (1:ℝ)/((((1:ℕ):ℝ) + 1) * Real.sqrt (((1:ℕ):ℝ) + 1)) + (1:ℝ)/((((2:ℕ):ℝ) + 1) * Real.sqrt (((2:ℕ):ℝ) + 1)) + (1:ℝ)/((((3:ℕ):ℝ) + 1) * Real.sqrt (((3:ℕ):ℝ) + 1)) + (1:ℝ)/((((4:ℕ):ℝ) + 1) * Real.sqrt (((4:ℕ):ℝ) + 1)) + (1:ℝ)/((((5:ℕ):ℝ) + 1) * Real.sqrt (((5:ℕ):ℝ) + 1)) + (1:ℝ)/((((6:ℕ):ℝ) + 1) * Real.sqrt (((6:ℕ):ℝ) + 1)) + (1:ℝ)/((((7:ℕ):ℝ) + 1) * Real.sqrt (((7:ℕ):ℝ) + 1)) + (1:ℝ)/((((8:ℕ):ℝ) + 1) * Real.sqrt (((8:ℕ):ℝ) + 1)) + (1:ℝ)/((((9:ℕ):ℝ) + 1) * Real.sqrt (((9:ℕ):ℝ) + 1)) + (1:ℝ)/((((10:ℕ):ℝ) + 1) * Real.sqrt (((10:ℕ):ℝ) + 1)) + (1:ℝ)/((((11:ℕ):ℝ) + 1) * Real.sqrt (((11:ℕ):ℝ) + 1)) + (1:ℝ)/((((12:ℕ):ℝ) + 1) * Real.sqrt (((12:ℕ):ℝ) + 1)) + (1:ℝ)/((((13:ℕ):ℝ) + 1) * Real.sqrt (((13:ℕ):ℝ) + 1)) + (1:ℝ)/((((14:ℕ):ℝ) + 1) * Real.sqrt (((14:ℕ):ℝ) + 1)) + (1:ℝ)/((((15:ℕ):ℝ) + 1) * Real.sqrt (((15:ℕ):ℝ) + 1)) + (1:ℝ)/((((16:ℕ):ℝ) + 1) * Real.sqrt (((16:ℕ):ℝ) + 1)) + (1:ℝ)/((((17:ℕ):ℝ) + 1) * Real.sqrt (((17:ℕ):ℝ) + 1)) + (1:ℝ)/((((18:ℕ):ℝ) + 1) * Real.sqrt (((18:ℕ):ℝ) + 1)) + (1:ℝ)/((((19:ℕ):ℝ) + 1) * Real.sqrt (((19:ℕ):ℝ) + 1)) + (1:ℝ)/((((20:ℕ):ℝ) + 1) * Real.sqrt (((20:ℕ):ℝ) + 1)) + (1:ℝ)/((((21:ℕ):ℝ) + 1) * Real.sqrt (((21:ℕ):ℝ) + 1)) + (1:ℝ)/((((22:ℕ):ℝ) + 1) * Real.sqrt (((22:ℕ):ℝ) + 1)) + (1:ℝ)/((((23:ℕ):ℝ) + 1) * Real.sqrt (((23:ℕ):ℝ) + 1)) + (1:ℝ)/((((24:ℕ):ℝ) + 1) * Real.sqrt (((24:ℕ):ℝ) + 1)) + (1:ℝ)/((((25:ℕ):ℝ) + 1) * Real.sqrt (((25:ℕ):ℝ) + 1)) + (1:ℝ)/((((26:ℕ):ℝ) + 1) * Real.sqrt (((26:ℕ):ℝ) + 1)) + (1:ℝ)/((((27:ℕ):ℝ) + 1) * Real.sqrt (((27:ℕ):ℝ) + 1)) + (1:ℝ)/((((28:ℕ):ℝ) + 1) * Real.sqrt (((28:ℕ):ℝ) + 1)) + (1:ℝ)/((((29:ℕ):ℝ) + 1) * Real.sqrt (((29:ℕ):ℝ) + 1)) + (1:ℝ)/((((30:ℕ):ℝ) + 1) * Real.sqrt (((30:ℕ):ℝ) + 1)) + (1:ℝ)/((((31:ℕ):ℝ) + 1) * Real.sqrt (((31:ℕ):ℝ) + 1)) + (1:ℝ)/((((32:ℕ):ℝ) + 1) * Real.sqrt (((32:ℕ):ℝ) + 1)) + (1:ℝ)/((((33:ℕ):ℝ) + 1) * Real.sqrt (((33:ℕ):ℝ) + 1)) + (1:ℝ)/((((34:ℕ):ℝ) + 1) * Real.sqrt (((34:ℕ):ℝ) + 1)) + (1:ℝ)/((((35:ℕ):ℝ) + 1) * Real.sqrt (((35:ℕ):ℝ) + 1)) + (1:ℝ)/((((36:ℕ):ℝ) + 1) * Real.sqrt (((36:ℕ):ℝ) + 1)) + (1:ℝ)/((((37:ℕ):ℝ) + 1) * Real.sqrt (((37:ℕ):ℝ) + 1)) + (1:ℝ)/((((38:ℕ):ℝ) + 1) * Real.sqrt (((38:ℕ):ℝ) + 1)) + (1:ℝ)/((((39:ℕ):ℝ) + 1) * Real.sqrt (((39:ℕ):ℝ) + 1)) + (1:ℝ)/((((40:ℕ):ℝ) + 1) * Real.sqrt (((40:ℕ):ℝ) + 1)) + (1:ℝ)/((((41:ℕ):ℝ) + 1) * Real.sqrt (((41:ℕ):ℝ) + 1)) + (1:ℝ)/((((42:ℕ):ℝ) + 1) * Real.sqrt (((42:ℕ):ℝ) + 1)) + (1:ℝ)/((((43:ℕ):ℝ) + 1) * Real.sqrt (((43:ℕ):ℝ) + 1)) + (1:ℝ)/((((44:ℕ):ℝ) + 1) * Real.sqrt (((44:ℕ):ℝ) + 1)) + (1:ℝ)/((((45:ℕ):ℝ) + 1) * Real.sqrt (((45:ℕ):ℝ) + 1)) + (1:ℝ)/((((46:ℕ):ℝ) + 1) * Real.sqrt (((46:ℕ):ℝ) + 1)) + (1:ℝ)/((((47:ℕ):ℝ) + 1) * Real.sqrt (((47:ℕ):ℝ) + 1)) + (1:ℝ)/((((48:ℕ):ℝ) + 1) * Real.sqrt (((48:ℕ):ℝ) + 1)) + (1:ℝ)/((((49:ℕ):ℝ) + 1) * Real.sqrt (((49:ℕ):ℝ) + 1)) + (1:ℝ)/((((50:ℕ):ℝ) + 1) * Real.sqrt (((50:ℕ):ℝ) + 1)) + (1:ℝ)/((((51:ℕ):ℝ) + 1) * Real.sqrt (((51:ℕ):ℝ) + 1)) + (1:ℝ)/((((52:ℕ):ℝ) + 1) * Real.sqrt (((52:ℕ):ℝ) + 1)) + (1:ℝ)/((((53:ℕ):ℝ) + 1) * Real.sqrt (((53:ℕ):ℝ) + 1)) + (1:ℝ)/((((54:ℕ):ℝ) + 1) * Real.sqrt (((54:ℕ):ℝ) + 1)) + (1:ℝ)/((((55:ℕ):ℝ) + 1) * Real.sqrt (((55:ℕ):ℝ) + 1)) + (1:ℝ)/((((56:ℕ):ℝ) + 1) * Real.sqrt (((56:ℕ):ℝ) + 1)) + (1:ℝ)/((((57:ℕ):ℝ) + 1) * Real.sqrt (((57:ℕ):ℝ) + 1)) + (1:ℝ)/((((58:ℕ):ℝ) + 1) * Real.sqrt (((58:ℕ):ℝ) + 1)) + (1:ℝ)/((((59:ℕ):ℝ) + 1) * Real.sqrt (((59:ℕ):ℝ) + 1)) + (1:ℝ)/((((60:ℕ):ℝ) + 1) * Real.sqrt (((60:ℕ):ℝ) + 1)) + (1:ℝ)/((((61:ℕ):ℝ) + 1) * Real.sqrt (((61:ℕ):ℝ) + 1)) + (1:ℝ)/((((62:ℕ):ℝ) + 1) * Real.sqrt (((62:ℕ):ℝ) + 1)) + (1:ℝ)/((((63:ℕ):ℝ) + 1) * Real.sqrt (((63:ℕ):ℝ) + 1)) + (1:ℝ)/((((64:ℕ):ℝ) + 1) * Real.sqrt (((64:ℕ):ℝ) + 1)) + (1:ℝ)/((((65:ℕ):ℝ) + 1) * Real.sqrt (((65:ℕ):ℝ) + 1)) + (1:ℝ)/((((66:ℕ):ℝ) + 1) * Real.sqrt (((66:ℕ):ℝ) + 1)) + (1:ℝ)/((((67:ℕ):ℝ) + 1) * Real.sqrt (((67:ℕ):ℝ) + 1)) + (1:ℝ)/((((68:ℕ):ℝ) + 1) * Real.sqrt (((68:ℕ):ℝ) + 1)) + (1:ℝ)/((((69:ℕ):ℝ) + 1) * Real.sqrt (((69:ℕ):ℝ) + 1)) + (1:ℝ)/((((70:ℕ):ℝ) + 1) * Real.sqrt (((70:ℕ):ℝ) + 1)) + (1:ℝ)/((((71:ℕ):ℝ) + 1) * Real.sqrt (((71:ℕ):ℝ) + 1)) + (1:ℝ)/((((72:ℕ):ℝ) + 1) * Real.sqrt (((72:ℕ):ℝ) + 1)) + (1:ℝ)/((((73:ℕ):ℝ) + 1) * Real.sqrt (((73:ℕ):ℝ) + 1)) + (1:ℝ)/((((74:ℕ):ℝ) + 1) * Real.sqrt (((74:ℕ):ℝ) + 1)) + (1:ℝ)/((((75:ℕ):ℝ) + 1) * Real.sqrt (((75:ℕ):ℝ) + 1)) + (1:ℝ)/((((76:ℕ):ℝ) + 1) * Real.sqrt (((76:ℕ):ℝ) + 1)) + (1:ℝ)/((((77:ℕ):ℝ) + 1) * Real.sqrt (((77:ℕ):ℝ) + 1)) + (1:ℝ)/((((78:ℕ):ℝ) + 1) * Real.sqrt (((78:ℕ):ℝ) + 1)) + (1:ℝ)/((((79:ℕ):ℝ) + 1) * Real.sqrt (((79:ℕ):ℝ) + 1)) + (1:ℝ)/((((80:ℕ):ℝ) + 1) * Real.sqrt (((80:ℕ):ℝ) + 1)) + (1:ℝ)/((((81:ℕ):ℝ) + 1) * Real.sqrt (((81:ℕ):ℝ) + 1)) + (1:ℝ)/((((82:ℕ):ℝ) + 1) * Real.sqrt (((82:ℕ):ℝ) + 1)) + (1:ℝ)/((((83:ℕ):ℝ) + 1) * Real.sqrt (((83:ℕ):ℝ) + 1)) + (1:ℝ)/((((84:ℕ):ℝ) + 1) * Real.sqrt (((84:ℕ):ℝ) + 1)) + (1:ℝ)/((((85:ℕ):ℝ) + 1) * Real.sqrt (((85:ℕ):ℝ) + 1)) + (1:ℝ)/((((86:ℕ):ℝ) + 1) * Real.sqrt (((86:ℕ):ℝ) + 1)) + (1:ℝ)/((((87:ℕ):ℝ) + 1) * Real.sqrt (((87:ℕ):ℝ) + 1)) + (1:ℝ)/((((88:ℕ):ℝ) + 1) * Real.sqrt (((88:ℕ):ℝ) + 1)) + (1:ℝ)/((((89:ℕ):ℝ) + 1) * Real.sqrt (((89:ℕ):ℝ) + 1)) + (1:ℝ)/((((90:ℕ):ℝ) + 1) * Real.sqrt (((90:ℕ):ℝ) + 1)) + (1:ℝ)/((((91:ℕ):ℝ) + 1) * Real.sqrt (((91:ℕ):ℝ) + 1)) + (1:ℝ)/((((92:ℕ):ℝ) + 1) * Real.sqrt (((92:ℕ):ℝ) + 1)) + (1:ℝ)/((((93:ℕ):ℝ) + 1) * Real.sqrt (((93:ℕ):ℝ) + 1)) + (1:ℝ)/((((94:ℕ):ℝ) + 1) * Real.sqrt (((94:ℕ):ℝ) + 1)) + (1:ℝ)/((((95:ℕ):ℝ) + 1) * Real.sqrt (((95:ℕ):ℝ) + 1)) + (1:ℝ)/((((96:ℕ):ℝ) + 1) * Real.sqrt (((96:ℕ):ℝ) + 1)) + (1:ℝ)/((((97:ℕ):ℝ) + 1) * Real.sqrt (((97:ℕ):ℝ) + 1)) + (1:ℝ)/((((98:ℕ):ℝ) + 1) * Real.sqrt (((98:ℕ):ℝ) + 1)) + (1:ℝ)/((((99:ℕ):ℝ) + 1) * Real.sqrt (((99:ℕ):ℝ) + 1)) + (1:ℝ)/((((100:ℕ):ℝ) + 1) * Real.sqrt (((100:ℕ):ℝ) + 1)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have hfin : (2.4138592 : ℝ) ≤ (∑ n ∈ Finset.range 101, (1:ℝ)/(((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1))) := by
    rw [hexp]
    linarith [zb_0, zb_1, zb_2, zb_3, zb_4, zb_5, zb_6, zb_7, zb_8, zb_9, zb_10, zb_11, zb_12, zb_13, zb_14, zb_15, zb_16, zb_17, zb_18, zb_19, zb_20, zb_21, zb_22, zb_23, zb_24, zb_25, zb_26, zb_27, zb_28, zb_29, zb_30, zb_31, zb_32, zb_33, zb_34, zb_35, zb_36, zb_37, zb_38, zb_39, zb_40, zb_41, zb_42, zb_43, zb_44, zb_45, zb_46, zb_47, zb_48, zb_49, zb_50, zb_51, zb_52, zb_53, zb_54, zb_55, zb_56, zb_57, zb_58, zb_59, zb_60, zb_61, zb_62, zb_63, zb_64, zb_65, zb_66, zb_67, zb_68, zb_69, zb_70, zb_71, zb_72, zb_73, zb_74, zb_75, zb_76, zb_77, zb_78, zb_79, zb_80, zb_81, zb_82, zb_83, zb_84, zb_85, zb_86, zb_87, zb_88, zb_89, zb_90, zb_91, zb_92, zb_93, zb_94, zb_95, zb_96, zb_97, zb_98, zb_99, zb_100]
  have htail : (0.1985148 : ℝ) ≤ (∑' (n : ℕ), (1:ℝ)/(((↑(n+101) : ℝ)+1) * Real.sqrt ((↑(n+101) : ℝ)+1))) := by
    have hpt : ∀ n : ℕ, G (n + 101) - G (n + 1 + 101) ≤
        (1:ℝ)/(((↑(n+101) : ℝ)+1) * Real.sqrt ((↑(n+101) : ℝ)+1)) := by
      intro n
      have h := trap_step (n + 101) (by omega)
      have he : ((n + 101) + 1 : ℕ) = n + 1 + 101 := by omega
      rw [he] at h
      simpa only [hG] using h
    have htel : ∀ K : ℕ, (∑ n ∈ Finset.range K, (G (n + 101) - G (n + 1 + 101))) =
        G 101 - G (K + 101) := by
      intro K
      have h := Finset.sum_range_sub' (fun n : ℕ => G (n + 101)) K
      simpa [Nat.add_assoc] using h
    have hzero : Tendsto (fun K : ℕ => G (K + 101)) atTop (nhds 0) := by
      have h := tendsto_G.comp (tendsto_add_atTop_nat 101)
      simpa only [Function.comp_def, hG] using h
    have hlim2 : Tendsto (fun K : ℕ => G 101 - G (K + 101)) atTop (nhds (G 101 - 0)) :=
      tendsto_const_nhds.sub hzero
    have hlim : Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K,
        (1:ℝ)/(((↑(n+101) : ℝ)+1) * Real.sqrt ((↑(n+101) : ℝ)+1))) atTop
        (nhds (∑' (n : ℕ), (1:ℝ)/(((↑(n+101) : ℝ)+1) * Real.sqrt ((↑(n+101) : ℝ)+1)))) :=
      (summable_nat_add_iff 101).mpr summ |>.tendsto_sum_tsum_nat
    have hmain := le_of_tendsto_of_tendsto' hlim2 hlim
      (fun K => by rw [← htel K]; exact Finset.sum_le_sum (fun n _ => hpt n))
    have hG101 : (0.1985148 : ℝ) ≤ G 101 := by
      have hGv : G 101 = 2 / Real.sqrt (102:ℝ) + (1/2)/((102:ℝ) * Real.sqrt (102:ℝ)) := by
        rw [hG]; norm_num
      rw [hGv]
      have hq : Real.sqrt (102:ℝ) ≤ (10099504939:ℝ)/1000000000 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      have hp : (0:ℝ) < Real.sqrt (102:ℝ) := Real.sqrt_pos.mpr (by norm_num)
      have h1 : (2:ℝ) / ((10099504939:ℝ)/1000000000) ≤ 2 / Real.sqrt 102 := by
        have h' := one_div_le_one_div_of_le hp hq
        have h2 := mul_le_mul_of_nonneg_left h' (by norm_num : (0:ℝ) ≤ 2)
        simpa [div_eq_mul_inv, mul_comm] using h2
      have h2 : (1/2:ℝ) / (102 * ((10099504939:ℝ)/1000000000)) ≤
          (1/2) / (102 * Real.sqrt 102) := by
        have hp2 : (0:ℝ) < 102 * Real.sqrt 102 := by positivity
        have hle : 102 * Real.sqrt 102 ≤ 102 * ((10099504939:ℝ)/1000000000) := by
          have h' := mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ) ≤ 102)
          linarith
        exact div_le_div_of_nonneg_left (by norm_num) hp2 hle
      have h3 : (0.1985148:ℝ) ≤ 2 / ((10099504939:ℝ)/1000000000) +
          (1/2) / (102 * ((10099504939:ℝ)/1000000000)) := by norm_num
      linarith
    linarith
  calc (2.61237:ℝ) ≤ 2.4138592 + 0.1985148 := by norm_num
    _ ≤ _ := add_le_add hfin htail


/-- LEAF: P0014 page 34, display 4.11, "ζ'(3/2) can be evaluated by Euler-Maclaurin":
|ζ'(3/2)| ≤ 3.9323. The true value is -3.9322397374..., margin 6.0e-5.
Class HARD: a certified Euler-Maclaurin evaluation of the derivative with remainder. -/
theorem deriv_zeta_three_half_le : ‖deriv riemannZeta (3 / 2)‖ ≤ 3.9323 := by
  sorry

/-- P0014 page 34, display 4.11: |ζ'(3/2)/ζ(3/2)| ≤ 1.50527, from the two Euler-Maclaurin
leaves; 3.9323/2.61237 = 1.505261. -/
theorem zeta_ratio_le : ‖deriv riemannZeta (3 / 2) / riemannZeta (3 / 2)‖ ≤ 1.50527 := by
  have h1 := zeta_three_half_ge
  have h2 := deriv_zeta_three_half_le
  have h3 : (2.61237 : ℝ) ≤ ‖riemannZeta (3 / 2)‖ := h1.trans (Complex.re_le_norm _)
  rw [norm_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- P0014 page 34, display 4.12, for primitive χ mod q, on s = -1/2 + iτ:
|L'/L(s, χ)| ≤ |log(q/π)| + (1/2) log(τ² + 9/4) + 4.1396.
Assembled from the leaves of this file and of `Prep1121VIPointwiseA`. -/
theorem pointwise_4_12 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (τ : ℝ) :
    ‖deriv χ.LFunction ((-1 / 2 : ℂ) + τ * I) / χ.LFunction ((-1 / 2 : ℂ) + τ * I)‖ ≤
      |Real.log (q / Real.pi)| + (1 / 2) * Real.log (τ ^ 2 + 9 / 4) + 4.1396 := by
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, (χ.Even ∧ κ = 0) ∨ (χ.Odd ∧ κ = 1) := by
    rcases χ.even_or_odd with h | h
    · exact ⟨0, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨1, Or.inr ⟨h, rfl⟩⟩
  have hκ' : κ = 0 ∨ κ = 1 := by rcases hκ with h | h <;> simp [h.2]
  set s : ℂ := (-1 / 2 : ℂ) + τ * I with hs
  have hz : (1 - s).re = 3 / 2 := by simp [hs]; norm_num
  have hψ := psi_sub_log_le (1 - s) hz
  have hC := log_cot_cancel τ κ hκ' (arctan_le_pi_tanh)
  have hD := (logDeriv_three_half_le χ⁻¹ τ).trans zeta_ratio_le
  have hnorm : ‖1 - s‖ = Real.sqrt (τ ^ 2 + 9 / 4) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp [hs]; ring
  have hlog : Real.log ‖1 - s‖ = (1 / 2) * Real.log (τ ^ 2 + 9 / 4) := by
    rw [hnorm, Real.log_sqrt (by positivity)]; ring
  have hq : ‖((Real.log (Real.pi / q) : ℝ) : ℂ)‖ = |Real.log (q / Real.pi)| := by
    rw [Complex.norm_real, Real.norm_eq_abs, ← abs_neg, ← Real.log_inv, inv_div]
  have h2 : ‖Complex.log 2‖ ≤ 0.6931471808 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num),
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos (by norm_num))]
    exact Real.log_two_lt_d9.le
  have hpi := Real.pi_lt_d6
  rw [fe_line hχ τ κ hκ]
  set A := ((Real.log (Real.pi / q) : ℝ) : ℂ)
  set Ψ := digamma (1 - s)
  set K := ((Real.pi / 2 : ℝ) : ℂ) * cot ((Real.pi : ℂ) * (s + κ) / 2)
  set D := logDeriv (χ⁻¹).LFunction (1 - s)
  have he : A + (-Ψ + Complex.log 2 + K) - D =
      A + (-Complex.log (1 - s) + K) + -(Ψ - Complex.log (1 - s)) + Complex.log 2 + -D := by
    ring
  rw [he]
  calc ‖A + (-Complex.log (1 - s) + K) + -(Ψ - Complex.log (1 - s)) + Complex.log 2 + -D‖
      ≤ ‖A‖ + ‖-Complex.log (1 - s) + K‖ + ‖Ψ - Complex.log (1 - s)‖ + ‖Complex.log 2‖ +
          ‖D‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        gcongr
        exact norm_add_le _ _
    _ ≤ |Real.log (q / Real.pi)| + ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + Real.pi / 2) +
          10 / 27 + 0.6931471808 + 1.50527 := by
        rw [hq, ← hlog]
        gcongr
    _ ≤ |Real.log (q / Real.pi)| + (1 / 2) * Real.log (τ ^ 2 + 9 / 4) + 4.1396 := by
        linarith

end LeanLab.HelfgottMajor.Prep1121VIPointwise
