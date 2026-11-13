import LeanLab.HelfgottMajor.Lemma41Terms
import LeanLab.HelfgottArcs.Statements
import LeanLab.HelfgottMajor.Gaussian123Base

/-!
P0014 Proposition 4.6, pages 43 and 44, display 4.43, with the recorded factor 6 repair.
This file proves the three statements the lab and Decomp123 refer to from the LEAF pieces of
Gaussian123Base, which holds the shared development: the explicit formula with its residue
bound, Lemma 4.4 for the zeros up to T and Lemma 4.5 for the zeros above T. Every statement
here is the one Decomp123 and the rest of the lab already use, unchanged, in the namespace
LeanLab.HelfgottMajor.SplitGaussian123.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real LeanLab.HelfgottArcs

/-- PROVED from the LEAF pieces of Gaussian123Base. P0014 Lemma 4.1, pages 31 to 36, displays 4.1 to 4.3 and 4.23, as specialized
on page 44 in the proof of Proposition 4.6: the explicit formula with residue
abs R at most 3 log q + 13.347 abs delta + 16.695 and contour error
(log q + 6.01)(1 + 6 abs delta) x^(-1/2), the factor 6 being the recorded repair F-5032. -/
theorem explicit_formula_remainder (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  -- Route burst session 9: Lemma 4.1 with R of display 4.2, then display 4.23 and page 44.
  exact explicit_formula_of_pieces x hx q χ hχ δ T hT

/-- PROVED from the LEAF pieces of Gaussian123Base. P0014 Lemma 4.4, display 4.29 on page 39, with the norms of display 4.42,
as applied on page 43: the zeros up to T, all on the critical line by hzeros, contribute
(2.337 sqrt T log qT + 21.817 sqrt T + 2.85 log q + 74.38) sqrt x. -/
theorem low_zero_bound (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38) * sqrt x := by
  -- Route burst session 9: split at height 1 as on page 39, then the arithmetic of page 43.
  apply low_zero_bound_of_mass χ δ x T _ (by linarith) hzeros
  rw [mass_split χ δ T]
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hv := very_low_mass_bound q χ hχ δ T hT1 hzeros
  have hm := middle_mass_bound q χ hχ δ T hT1 hzeros
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hlogqT : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have ha := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0_log
    (mul_nonneg (sqrt_nonneg T) hlogqT)
  have hb := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0 (sqrt_nonneg T)
  obtain ⟨hc, hd⟩ := Sec45.coef_logq
  nlinarith

/-- PROVED from the LEAF pieces of Gaussian123Base. P0014 Lemma 4.5, pages 40 to 43, display 4.35 and its use on page 43:
the zeros above T contribute log(qT/2π)(4.329 e^(-0.1598 T)
+ 0.802 abs delta e^(-0.1065 (T/(π abs delta))^2)) x. -/
theorem high_zero_bound (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖highZeros χ δ x T‖ ≤
      log (q * T / (2 * π)) *
        (4.329 * exp (-0.1598 * T) +
          0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x := by
  -- Route burst session 9: display 4.35 bound, then displays 4.36 and 4.41, page 42.
  obtain ⟨hs, hm⟩ := tail_mass_integral q χ hχ δ T hT hzeros
  apply high_zero_bound_of_mass χ δ x T _ hx hs
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have he := TailIntegral123.exp_integral_bound q T hT100
  have hg : TailIntegral123.gaussianTailIntegral q δ T ≤
      0.18787 * |δ| * log (q * T / (2 * π)) *
        exp (-0.1065 * (T / (π * |δ|)) ^ 2) := by
    by_cases hδ : δ = 0
    · simp [hδ, TailIntegral123.gaussianTailIntegral]
    · exact TailIntegral123.gaussian_integral_bound q δ T hδ hT
  have hlog : 0 ≤ log ((q : ℝ) * T / (2 * π)) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    apply log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pi_lt_four]
  calc
    _ ≤ 4.226 * (TailIntegral123.expTailIntegral q T +
          TailIntegral123.gaussianTailIntegral q δ T) := hm
    _ ≤ 4.226 * (1.0242 * log (q * T / (2 * π)) * exp (-0.1598 * T) +
        0.18787 * |δ| * log (q * T / (2 * π)) *
          exp (-0.1065 * (T / (π * |δ|)) ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add he hg) (by norm_num)
    _ ≤ _ := by
      nlinarith [mul_nonneg hlog (exp_pos (-0.1598 * T)).le,
        mul_nonneg hlog (mul_nonneg (abs_nonneg δ)
          (exp_pos (-0.1065 * (T / (π * |δ|)) ^ 2)).le)]

end LeanLab.HelfgottMajor.SplitGaussian123
