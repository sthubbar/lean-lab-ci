/-
Final error budgets for the sealed major arc statements.
Source: https://arxiv.org/abs/1305.2897v4, Section 4.6, pages 57 to 59.
AI wrote this Lean code for CODEX task81. Binary Goldbach is open.
The analytic estimates passed as hypotheses remain CONDITIONAL inputs.
-/
import LeanLab.HelfgottArcs.Statements
import LeanLab.HelfgottMajor.Assembly

namespace LeanLab.HelfgottArcs
open Real

/-- The last numerical reduction for the Gaussian, with the actual variable x. -/
theorem gaussian_error_terms_le {q x : ℝ} (hq : 1 ≤ q) (hx : 10 ^ 8 ≤ x) :
    5.281e-22 + (648662 / √q + 111) / √x + (55 + 1.7e7 / q) / x +
      (19 + 1.2e8 / q) / (x * √x) ≤
        5.281e-22 + 1 / √x * (650400 / √q + 112) := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < √x := Real.sqrt_pos.mpr hx0
  have hs : (1e4 : ℝ) ≤ √x := by
    rw [Real.le_sqrt (by norm_num) hx0.le]
    norm_num at hx ⊢
    exact hx
  have h := LeanLab.HelfgottMajor.A7 hq hs
  have hmul := div_le_div_of_nonneg_right h hs0.le
  have heq :
      (648662 / √q + 111 + (55 + 1.7e7 / q) / √x + (19 + 1.2e8 / q) / (√x) ^ 2) / √x =
      (648662 / √q + 111) / √x + (55 + 1.7e7 / q) / x + (19 + 1.2e8 / q) / (x * √x) := by
    generalize hroot : √x = s
    have hxx : x = s ^ 2 := by rw [← hroot, Real.sq_sqrt hx0.le]
    rw [hxx]
    ring
  rw [heq] at hmul
  have hfinal := add_le_add_left hmul (5.281e-22 : ℝ)
  simp only [div_eq_mul_inv, one_mul] at hfinal ⊢
  linarith

/-- Theorem 1.1, CONDITIONAL ON its intermediate analytic estimate on page 57. -/
theorem major_1_1_of_error_terms (x : ℝ) (hx : 10 ^ 8 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (hGaussian : MajorShape etaHeart χ δ x
      (5.281e-22 + (648662 / √q + 111) / √x + (55 + 1.7e7 / q) / x +
        (19 + 1.2e8 / q) / (x * √x))) :
    MajorShape etaHeart χ δ x (5.281e-22 + 1 / √x * (650400 / √q + 112)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  exact hGaussian.trans (mul_le_mul_of_nonneg_right (gaussian_error_terms_le hq hx)
    (by linarith))

/-- All numerical leaves of Proposition 4.6 at T0 = 10^8/q. -/
theorem gaussian_explicit_error_le {q d x u : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hd0 : 0 ≤ d) (hd : d ≤ 1.2e6 / q) (hx : 10 ^ 8 ≤ x)
    (hu : 1000 / (12 * π) ≤ u) :
    log (1e8 / (2 * π)) * (4.329 * exp (-0.1598 * (1e8 / q)) +
        0.802 * d * exp (-0.1065 * u ^ 2)) +
      (2.337 * √(1e8 / q) * log (q * (1e8 / q)) + 21.817 * √(1e8 / q) +
        2.85 * log q + 74.38) / √x +
      (3 * log q + 14 * d + 17) / x + (log q + 6) * (1 + 5 * d) / (x * √x) ≤
      5.281e-22 + 1 / √x * (650400 / √q + 112) := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 < x := by linarith
  have hT : (1000 : ℝ) / 3 ≤ 1e8 / q := by
    rw [le_div_iff₀ hq0]
    nlinarith
  have hd1 : d ≤ 1.2e6 := by
    have hdq := (le_div_iff₀ hq0).mp hd
    nlinarith
  have hlog0 : 0 ≤ log (1e8 / (2 * π)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_four]
  have he1 := LeanLab.HelfgottMajor.A1 hT
  have he2 := LeanLab.HelfgottMajor.A2 hu
  have he : log (1e8 / (2 * π)) * (4.329 * exp (-0.1598 * (1e8 / q)) +
      0.802 * d * exp (-0.1065 * u ^ 2)) ≤ 5.281e-22 := by
    have hinner : 4.329 * exp (-0.1598 * (1e8 / q)) +
        0.802 * d * exp (-0.1065 * u ^ 2) ≤ 3.184e-23 + 1.2e6 * 4.3166e-33 := by
      have hmul := mul_le_mul_of_nonneg_left he2 hd0
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hinner hlog0
    obtain ⟨a, b, c⟩ := LeanLab.HelfgottMajor.A3
    nlinarith
  have hq' : q ≤ 3e5 := by norm_num at *; exact hq
  have hz := div_le_div_of_nonneg_right (LeanLab.HelfgottMajor.A4 hq1 hq') (sqrt_nonneg x)
  obtain ⟨ha, hb⟩ := LeanLab.HelfgottMajor.A56 hq1 hq' hd0 hd
  have ha' := div_le_div_of_nonneg_right ha hx0.le
  have hb' := div_le_div_of_nonneg_right hb (show 0 ≤ x * √x by positivity)
  exact (show _ ≤ 5.281e-22 + (648662 / √q + 111) / √x + (55 + 1.7e7 / q) / x +
      (19 + 1.2e8 / q) / (x * √x) by linarith).trans (gaussian_error_terms_le hq1 hx)

/-- The corrected 5.056 coefficient still gives the printed Theorem 1.2 budget. -/
theorem t2_corrected_sqrt_terms_le {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000) :
    1.22 * √(1e8 / q) * log (q * (1e8 / q)) + 5.056 * √(1e8 / q) +
      1.423 * log q + 37.19 + (0.0004 + 1322 / q) ≤ 276600 / √q + 56 := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < √q := sqrt_pos.mpr hq0
  have hs1 : 1 ≤ √q := Real.one_le_sqrt.mpr hq1
  have hsle : √q ≤ q := by nlinarith [sq_sqrt hq0.le]
  have h1322 : (1322 : ℝ) / q ≤ 1322 / √q :=
    div_le_div_of_nonneg_left (by norm_num) hs0 hsle
  have hcore : 1.22 * √(1e8 / q) * log (q * (1e8 / q)) + 5.056 * √(1e8 / q) ≤
      275293 / √q := by
    rw [LeanLab.HelfgottMajor.sqrt_T0 hq0,
      show q * (1e8 / q) = 1e8 by field_simp]
    have heq : 1.22 * (1e4 / √q) * log 1e8 + 5.056 * (1e4 / √q) =
        (12200 * log 1e8 + 50560) / √q := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith [LeanLab.HelfgottMajor.log_1e8_lt]) hs0.le
  have hroom : 15 / √q + 1.423 * log q + 37.1904 ≤ 56 := by
    by_cases h10 : q ≤ 10
    · have hl : log q ≤ 2.3025854 :=
        (log_le_log hq0 h10).trans LeanLab.HelfgottMajor.log_ten_lt.le
      have hi : (15 : ℝ) / √q ≤ 15 := (div_le_iff₀ hs0).mpr (by linarith)
      linarith
    · by_cases h1000 : q ≤ 1000
      · have hl : log q ≤ 3 * log 10 := by
          have hh := log_le_log hq0 h1000
          rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, log_pow] at hh
          norm_num at hh
          exact hh
        have hs3 : 3 ≤ √q := (le_sqrt (by norm_num) hq0.le).mpr (by linarith)
        have hi : (15 : ℝ) / √q ≤ 5 := (div_le_iff₀ hs0).mpr (by linarith)
        linarith [LeanLab.HelfgottMajor.log_ten_lt]
      · have hs30 : 30 ≤ √q := (le_sqrt (by norm_num) hq0.le).mpr (by linarith)
        have hi : (15 : ℝ) / √q ≤ 0.5 := (div_le_iff₀ hs0).mpr (by linarith)
        have hl := LeanLab.HelfgottMajor.log_q_le hq1 (show q ≤ 3e5 by norm_num at *; exact hq)
        linarith
  have heq : (276600 : ℝ) / √q = 275293 / √q + 1322 / √q - 15 / √q := by ring
  rw [heq]
  linarith

/-- The corrected Theorem 1.2 error budget, with all lower order terms. -/
theorem t2_corrected_error_terms_le {q d x : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hd0 : 0 ≤ d) (hd : d ≤ 1.2e6 / q) (hx : 10 ^ 8 ≤ x) :
    4.269e-14 / q +
      (1.22 * √(1e8 / q) * log (q * (1e8 / q)) + 5.056 * √(1e8 / q) +
        1.423 * log q + 37.19) / √x +
      (3 + 11 * d) / x + (log q + 6) * (1 + 6 * d) / (x * √x) ≤
      4.269e-14 / q + 1 / √x * (276600 / √q + 56) := by
  have hx0 : 0 < x := by linarith
  have hs : (1e4 : ℝ) ≤ √x := by
    rw [le_sqrt (by norm_num) hx0.le]
    norm_num at hx ⊢
    exact hx
  have hq' : q ≤ 3e5 := by norm_num at *; exact hq
  have hb := (LeanLab.HelfgottMajor.B45 hq1 hq' hd0 hd hs).1
  have hz := t2_corrected_sqrt_terms_le hq1 hq
  have hall :
      (1.22 * √(1e8 / q) * log (q * (1e8 / q)) + 5.056 * √(1e8 / q) +
        1.423 * log q + 37.19) + (3 + 11 * d) / √x +
          (log q + 6) * (1 + 6 * d) / (√x) ^ 2 ≤ 276600 / √q + 56 := by linarith
  have hh := div_le_div_of_nonneg_right hall (sqrt_nonneg x)
  have heq :
      ((1.22 * √(1e8 / q) * log (q * (1e8 / q)) + 5.056 * √(1e8 / q) +
        1.423 * log q + 37.19) + (3 + 11 * d) / √x +
          (log q + 6) * (1 + 6 * d) / (√x) ^ 2) / √x =
      (1.22 * √(1e8 / q) * log (q * (1e8 / q)) + 5.056 * √(1e8 / q) +
        1.423 * log q + 37.19) / √x +
      (3 + 11 * d) / x + (log q + 6) * (1 + 6 * d) / (x * √x) := by
    generalize hroot : √x = s
    have hxx : x = s ^ 2 := by rw [← hroot, sq_sqrt hx0.le]
    rw [hxx]
    ring
  rw [heq] at hh
  have hh' := add_le_add_left hh (4.269e-14 / q)
  simp only [div_eq_mul_inv, one_mul] at hh' ⊢
  linarith

/-- The corrected Corollary 1.3 coefficient fits the original constants. -/
theorem convolution_corrected_sqrt_terms_le {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000) :
    1.675 * √(1e8 / q) * log (q * (1e8 / q)) + (5.056 * 1.37259) * √(1e8 / q) +
      1.954 * log q + 51.047 + (0.0007 + 2644 / q) ≤ 380600 / √q + 76 := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < √q := sqrt_pos.mpr hq0
  have hsle : √q ≤ q := by nlinarith [sq_sqrt hq0.le]
  have hr : (2644 : ℝ) / q ≤ 2644 / √q :=
    div_le_div_of_nonneg_left (by norm_num) hs0 hsle
  have hcore : 1.675 * √(1e8 / q) * log (q * (1e8 / q)) +
      (5.056 * 1.37259) * √(1e8 / q) ≤ 377945 / √q := by
    rw [LeanLab.HelfgottMajor.sqrt_T0 hq0,
      show q * (1e8 / q) = 1e8 by field_simp]
    have heq : 1.675 * (1e4 / √q) * log 1e8 + (5.056 * 1.37259) * (1e4 / √q) =
        (16750 * log 1e8 + (5.056 * 1.37259) * 1e4) / √q := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith [LeanLab.HelfgottMajor.log_1e8_lt]) hs0.le
  have hl := LeanLab.HelfgottMajor.log_q_le hq1 (show q ≤ 3e5 by norm_num at *; exact hq)
  have heq : (380600 : ℝ) / √q = 377945 / √q + 2644 / √q + 11 / √q := by ring
  rw [heq]
  have hi : (0 : ℝ) ≤ 11 / √q := by positivity
  linarith

/-- The corrected Corollary 1.3 error budget, with all lower order terms. -/
theorem convolution_corrected_error_terms_le {q d x : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hd0 : 0 ≤ d) (hd : d ≤ 1.2e6 / q) (hx : 10 ^ 8 ≤ x) :
    4.269e-14 / q +
      (1.675 * √(1e8 / q) * log (q * (1e8 / q)) + (5.056 * 1.37259) * √(1e8 / q) +
        1.954 * log q + 51.047) / √x +
      (6 + 22 * d) / x + (log q + 6) * (3 + 17 * d) / (x * √x) ≤
      4.269e-14 / q + 1 / √x * (380600 / √q + 76) := by
  have hx0 : 0 < x := by linarith
  have hs : (1e4 : ℝ) ≤ √x := by
    rw [le_sqrt (by norm_num) hx0.le]
    norm_num at hx ⊢
    exact hx
  have hq' : q ≤ 3e5 := by norm_num at *; exact hq
  have hb := (LeanLab.HelfgottMajor.B45 hq1 hq' hd0 hd hs).2
  have hz := convolution_corrected_sqrt_terms_le hq1 hq
  have hall :
      (1.675 * √(1e8 / q) * log (q * (1e8 / q)) + (5.056 * 1.37259) * √(1e8 / q) +
        1.954 * log q + 51.047) + (6 + 22 * d) / √x +
          (log q + 6) * (3 + 17 * d) / (√x) ^ 2 ≤ 380600 / √q + 76 := by linarith
  have hh := div_le_div_of_nonneg_right hall (sqrt_nonneg x)
  have heq :
      ((1.675 * √(1e8 / q) * log (q * (1e8 / q)) + (5.056 * 1.37259) * √(1e8 / q) +
        1.954 * log q + 51.047) + (6 + 22 * d) / √x +
          (log q + 6) * (3 + 17 * d) / (√x) ^ 2) / √x =
      (1.675 * √(1e8 / q) * log (q * (1e8 / q)) + (5.056 * 1.37259) * √(1e8 / q) +
        1.954 * log q + 51.047) / √x +
      (6 + 22 * d) / x + (log q + 6) * (3 + 17 * d) / (x * √x) := by
    generalize hroot : √x = s
    have hxx : x = s ^ 2 := by rw [← hroot, sq_sqrt hx0.le]
    rw [hxx]
    ring
  rw [heq] at hh
  have hh' := add_le_add_left hh (4.269e-14 / q)
  simp only [div_eq_mul_inv, one_mul] at hh' ⊢
  linarith

/-- Theorem 1.4's final reduction with the corrected factor 1.32 times 10^7. -/
theorem etaPlus_error_terms_le {q x : ℝ} (hq : 1 ≤ q) (hx : 10 ^ 12 ≤ x) :
    6.18e-12 / √q + 1.14e-10 / q +
      (499076 / √q + 51.17 + 1.32e7 / (q * √x) + 9 / √x +
        9.1e7 / (q * x) + 139 / x) / √x ≤
      6.18e-12 / √q + 1.14e-10 / q + 1 / √x * (499100 / √q + 52) := by
  have hx0 : 0 < x := by linarith
  have hs : (1e6 : ℝ) ≤ √x := by
    rw [le_sqrt (by norm_num) hx0.le]
    norm_num at hx ⊢
    exact hx
  have hh := LeanLab.HelfgottMajor.C4_final hq hs
  rw [sq_sqrt hx0.le] at hh
  have hdiv := div_le_div_of_nonneg_right hh (sqrt_nonneg x)
  have hadd := add_le_add_left hdiv (6.18e-12 / √q + 1.14e-10 / q)
  simp only [div_eq_mul_inv, one_mul] at hadd ⊢
  nlinarith

/-- The optimized etaPlus error at q = 1, including the numerical exponential tail. -/
theorem etaPlus_q1_error_terms_le {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    log ((1.2e7 * π + 200) / (2 * π)) *
        (exp (-1300000 * log 10) + 6773000 * exp (-0.1065 * 20 ^ 2)) +
      ((1.631 * log (1.2e7 * π + 200) + 12.42) * √(1.2e7 * π + 200) + 34.51) / √x +
        6600009 / x ≤ 3.34e-11 + 251100 / √x := by
  have hx0 : 0 < x := by linarith
  have hs : (1e6 : ℝ) ≤ √x := by
    rw [le_sqrt (by norm_num) hx0.le]
    norm_num at hx ⊢
    exact hx
  have htail := LeanLab.HelfgottMajor.C5c
  have hmain := LeanLab.HelfgottMajor.C5d hs
  have hh := div_le_div_of_nonneg_right hmain (sqrt_nonneg x)
  have heq :
      ((1.631 * log (1.2e7 * π + 200) + 12.42) * √(1.2e7 * π + 200) + 34.51 +
        6600009 / √x) / √x =
      ((1.631 * log (1.2e7 * π + 200) + 12.42) * √(1.2e7 * π + 200) + 34.51) / √x +
        6600009 / x := by
    generalize hroot : √x = s
    have hxx : x = s ^ 2 := by rw [← hroot, sq_sqrt hx0.le]
    rw [hxx]
    ring
  rw [heq] at hh
  linarith


/-- Theorem 1.2, CONDITIONAL ON the corrected Proposition 4.8 analytic estimate. -/
theorem major_1_2_of_error_terms (x : ℝ) (hx : 10 ^ 8 ≤ x) (q : ℕ) [NeZero q]
    (hq : q ≤ 300000) (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (hδ : |δ| ≤ 4 * 300000 / q)
    (hT2 : MajorShape etaT2 χ δ x
      (4.269e-14 / q +
        (1.22 * √(1e8 / q) * log (q * (1e8 / q)) + 5.056 * √(1e8 / q) +
          1.423 * log q + 37.19) / √x +
        (3 + 11 * |δ|) / x + (log q + 6) * (1 + 6 * |δ|) / (x * √x))) :
    MajorShape etaT2 χ δ x (4.269e-14 / q + 1 / √x * (276600 / √q + 56)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqr : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hd : |δ| ≤ 1.2e6 / q := by norm_num at hδ ⊢; exact hδ
  exact hT2.trans (mul_le_mul_of_nonneg_right
    (t2_corrected_error_terms_le hq1 hqr (abs_nonneg δ) hd hx) (by linarith))


/-- Corollary 1.3, CONDITIONAL ON the corrected Corollary 4.9 analytic estimate. -/
theorem major_1_3_of_error_terms (x : ℝ) (hx : 10 ^ 8 ≤ x) (q : ℕ) [NeZero q]
    (hq : q ≤ 300000) (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (hδ : |δ| ≤ 4 * 300000 / q)
    (hConvolution : MajorShape (mconv etaT2 (mconv eta1 eta1)) χ δ x
      (4.269e-14 / q +
        (1.675 * √(1e8 / q) * log (q * (1e8 / q)) + (5.056 * 1.37259) * √(1e8 / q) +
          1.954 * log q + 51.047) / √x +
        (6 + 22 * |δ|) / x + (log q + 6) * (3 + 17 * |δ|) / (x * √x))) :
    MajorShape (mconv etaT2 (mconv eta1 eta1)) χ δ x
      (4.269e-14 / q + 1 / √x * (380600 / √q + 76)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqr : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hd : |δ| ≤ 1.2e6 / q := by norm_num at hδ ⊢; exact hδ
  exact hConvolution.trans (mul_le_mul_of_nonneg_right
    (convolution_corrected_error_terms_le hq1 hqr (abs_nonneg δ) hd hx) (by linarith))


/-- Theorem 1.4, CONDITIONAL ON the corrected intermediate etaPlus estimate. -/
theorem major_1_4_of_error_terms (x : ℝ) (hx : 10 ^ 12 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (hPlus : MajorShape etaPlus χ δ x
      (6.18e-12 / √q + 1.14e-10 / q +
        (499076 / √q + 51.17 + 1.32e7 / (q * √x) + 9 / √x +
          9.1e7 / (q * x) + 139 / x) / √x)) :
    MajorShape etaPlus χ δ x
      (6.18e-12 / √q + 1.14e-10 / q + 1 / √x * (499100 / √q + 52)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  exact hPlus.trans (mul_le_mul_of_nonneg_right (etaPlus_error_terms_le hq1 hx) (by linarith))


/-- The sharper q = 1 result, CONDITIONAL ON the optimized equation 4.65 estimate. -/
theorem major_1_4_q1_of_error_terms (x : ℝ) (hx : 10 ^ 12 ≤ x)
    (χ : DirichletCharacter ℂ 1) (δ : ℝ)
    (hTrivial : MajorShape etaPlus χ δ x
      (log ((1.2e7 * π + 200) / (2 * π)) *
          (exp (-1300000 * log 10) + 6773000 * exp (-0.1065 * 20 ^ 2)) +
        ((1.631 * log (1.2e7 * π + 200) + 12.42) * √(1.2e7 * π + 200) + 34.51) / √x +
          6600009 / x)) :
    MajorShape etaPlus χ δ x (3.34e-11 + 251100 / √x) := by
  exact hTrivial.trans (mul_le_mul_of_nonneg_right (etaPlus_q1_error_terms_le hx) (by linarith))

end LeanLab.HelfgottArcs
