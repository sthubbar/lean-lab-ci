import LeanLab.ChirreHagen2025.Statements

/-!
P0075 page 4, the gamma estimate after equation 2.4.
Chandee Lemma 2.3 and its Appendix, preprint pages 12 and 13.
https://arxiv.org/abs/0906.4177
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp377d
open MeasureTheory

/-- Chandee page 12, the real Binet remainder integrand. -/
noncomputable def binetKernel (z : ℂ) (u : ℝ) : ℝ :=
  -(2 * u * (u ^ 2 + z.re ^ 2 - z.im ^ 2)) /
    (((u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2) *
      (Real.exp (2 * Real.pi * u) - 1))

/-- Chandee page 12, the real remainder I at z. -/
noncomputable def binetRemainder (z : ℂ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), binetKernel z u

/-- LEAF. Chandee Appendix page 12, first display and definition of I.
The cited formula is Ahlfors page 202. Integrability is explicit.
There is no sign estimate for the remainder in this leaf. -/
theorem binet_identity (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    IntegrableOn (binetKernel z) (Set.Ioi (0 : ℝ)) ∧
    (deriv Complex.Gamma z / Complex.Gamma z).re =
      Real.log ‖z‖ - (1 / (2 * z)).re + binetRemainder z := by
  sorry

/-- LEAF. Chandee Appendix pages 12 and 13, Case 1 and display 24.
The initial sign argument handles imaginary part squared at most real
part squared. Otherwise the integral split at norm z over three bounds
this correction on the unbounded region. There is no Gamma term. -/
theorem large_correction (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hn : 4 ≤ ‖z‖) :
    -(1 / (2 * z)).re + binetRemainder z ≤ 0 := by
  sorry

/-- LEAF. Chandee Appendix page 13, Case 2 and its final display.
The bounded region reduces to f at real part one quarter, followed by
the stated numerical verification. That input remains OPEN. The initial
sign argument handles the remaining imaginary parts. -/
theorem small_correction (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hn : ‖z‖ < 4) :
    -(1 / (2 * z)).re + binetRemainder z ≤ 0 := by
  sorry

/-- Chandee Lemma 2.3 from its three smaller Appendix inputs.
CONDITIONAL ON the Binet identity and the two remainder regions. -/
theorem gamma_log_derivative (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    (deriv Complex.Gamma z / Complex.Gamma z).re ≤ Real.log ‖z‖ := by
  rw [(binet_identity z hz).2]
  by_cases hn : 4 ≤ ‖z‖
  · linarith [large_correction z hz hn]
  · linarith [small_correction z hz (lt_of_not_ge hn)]

/-- P0075 page 4, chain-rule factor in the inherited composed-Gamma target. -/
theorem gamma_chain (s : ℂ) (hs : 0 ≤ s.re) :
    (deriv (fun z => Complex.Gamma (z / 2 + 1)) s / Complex.Gamma (s / 2 + 1)).re =
      (1 / 2 : ℝ) * (deriv Complex.Gamma (s / 2 + 1) / Complex.Gamma (s / 2 + 1)).re := by
  have hw : 0 < (s / 2 + 1).re := by simp [Complex.div_re]; linarith
  have hp : ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
    intro m hm
    have h := congrArg Complex.re hm
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hg : HasDerivAt (fun z : ℂ => z / 2 + 1) (1 / 2) s := by
    convert ((hasDerivAt_id s).div_const (2 : ℂ)).add_const 1 using 1 <;> simp
  have h := hg.logDeriv_Gamma hp
  simp only [logDeriv_apply, Complex.digamma_def] at h
  rw [h]
  simp [Complex.mul_re]

/-- P0075 page 4, elementary logarithm bound for the shifted argument. -/
theorem shifted_log_norm (s : ℂ) (hs : 0 ≤ s.re) (ht : s.im ≠ 0) :
    Real.log ‖s / 2 + 1‖ ≤ Real.log |s.im| - Real.log 2 +
      (s.re + 2) ^ 2 / (2 * s.im ^ 2) := by
  let w : ℂ := s / 2 + 1
  have hwre : 1 ≤ w.re := by simp [w, Complex.div_re]; linarith
  have hwn : 1 ≤ ‖w‖ := hwre.trans (Complex.re_le_norm w)
  have hw0 : 0 < ‖w‖ := by linarith
  have hn : ‖w‖ ^ 2 = ((s.re + 2) ^ 2 + s.im ^ 2) / 4 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [w, Complex.div_re, Complex.div_im]
    ring
  have ht2 : s.im ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have h := Real.log_le_sub_one_of_pos
    (by positivity : 0 < 4 * ‖w‖ ^ 2 / s.im ^ 2)
  have he : 4 * ‖w‖ ^ 2 / s.im ^ 2 - 1 = (s.re + 2) ^ 2 / s.im ^ 2 := by
    rw [hn]
    field_simp
    ring
  have hl : Real.log (4 * ‖w‖ ^ 2 / s.im ^ 2) =
      2 * Real.log 2 + 2 * Real.log ‖w‖ - 2 * Real.log s.im := by
    rw [Real.log_div (by positivity) ht2,
      Real.log_mul (by norm_num) (pow_ne_zero 2 hw0.ne'), Real.log_pow, Real.log_pow,
      show Real.log (4 : ℝ) = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num]
    norm_num
  rw [he, hl] at h
  change Real.log ‖w‖ ≤ _
  rw [Real.log_abs]
  have hdiv : (s.re + 2) ^ 2 / (2 * s.im ^ 2) = ((s.re + 2) ^ 2 / s.im ^ 2) / 2 := by ring
  rw [hdiv]
  linarith

/-- P0075 page 4, exact statement of DecompJ966.leaf_gamma_bound.
CONDITIONAL ON the three Chandee Appendix leaves. The inherited target
uses a composed derivative, so its factor one half is retained. -/
theorem leaf_gamma_bound (s : ℂ) (h_re : s.re ≥ 0) (h_im : s.im ≠ 0) :
    (deriv (fun z => Complex.Gamma (z / 2 + 1)) s / Complex.Gamma (s / 2 + 1)).re ≤
    Real.log |s.im| - Real.log 2 + (s.re + 2) ^ 2 / (2 * s.im ^ 2) := by
  have hr : 1 ≤ (s / 2 + 1).re := by simp [Complex.div_re]; linarith
  have hn : 1 ≤ ‖s / 2 + 1‖ := hr.trans (Complex.re_le_norm _)
  have hl : 0 ≤ Real.log ‖s / 2 + 1‖ := Real.log_nonneg hn
  have hg := gamma_log_derivative (s / 2 + 1) (by linarith)
  rw [gamma_chain s h_re]
  apply le_trans (show (1 / 2 : ℝ) *
    (deriv Complex.Gamma (s / 2 + 1) / Complex.Gamma (s / 2 + 1)).re ≤
      Real.log ‖s / 2 + 1‖ by linarith)
  exact shifted_log_norm s h_re h_im

end LeanLab.ChirreHagen2025.Decomp377d
