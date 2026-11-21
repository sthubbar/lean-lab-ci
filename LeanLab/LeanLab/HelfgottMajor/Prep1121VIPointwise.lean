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
  sorry

/-- LEAF: P0014 page 34, display 4.11, the comparison of Dirichlet series: on re w = 3/2,
|L'/L(w, χ)| ≤ Σ Λ(n) n^(-3/2) = |ζ'(3/2)/ζ(3/2)|. The comparison is already done in
`LeanLab.Linnik.ExplicitFormula.logDeriv_L_three_half_le` with an unnamed constant; Mathlib's
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div` names it. Class MEDIUM: one idea plus a
Mathlib lookup. -/
theorem logDeriv_three_half_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (τ : ℝ) :
    ‖logDeriv χ.LFunction (1 - ((-1 / 2 : ℂ) + τ * I))‖ ≤
      ‖deriv riemannZeta (3 / 2) / riemannZeta (3 / 2)‖ := by
  sorry

/-- LEAF: P0014 page 34, display 4.11, "ζ(3/2) can be evaluated by Euler-Maclaurin":
re ζ(3/2) ≥ 2.61237. The true value is 2.6123753486..., margin 5.3e-6.
Class HARD: a certified Euler-Maclaurin evaluation with explicit remainder. -/
theorem zeta_three_half_ge : (2.61237 : ℝ) ≤ (riemannZeta (3 / 2)).re := by
  sorry

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
