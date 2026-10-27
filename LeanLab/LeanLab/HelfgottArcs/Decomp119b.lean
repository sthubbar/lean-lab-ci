/-
P0013 page 76 Lemma A.5 and page 76 equation A.12.
The multiplier below is the Fourier transform of the distributional second derivative.
No distribution object is introduced in Lean.
The derived anchor proof uses rho equal to 4 and linearity in log rho.
AI wrote the Lean code for CODEX task119. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.FourierDecay

namespace LeanLab.HelfgottArcs.Decomp119b
open MeasureTheory Set Real

/-- CITED. P0013 page 76 Lemma A.5, expressed by the second Fourier multiplier. -/
def LemmaA5 : Prop := ∀ ρ : ℝ, 4 ≤ ρ → ∀ δ : ℝ,
  ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat (eta2rho ρ) δ‖ < 31.521 * log ρ

/-- LEAF. Page 75 Lemma A.2, the compact numerical verification left by task81. -/
theorem a2_compact (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 655) :
    ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ ≤ 31.521 := by
  sorry

/-- LEAF. Page 76 equation A.12, the weight is affine in log rho. -/
theorem weight_affine (ρ t : ℝ) (hρ : 4 ≤ ρ) :
    eta2rho ρ t = (log ρ - log 4) * eta2 t + eta2rho 4 t := by
  by_cases ht : 0 < t
  · have hr : 0 < ρ := by linarith
    simp only [eta2rho, Real.log_mul hr.ne' ht.ne',
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) ht.ne']
    ring
  · simp [eta2rho, eta2, ht]

/-- LEAF. Page 76 equation A.12, Fourier linearity for the affine weight. -/
theorem fourier_affine (ρ δ : ℝ) (hρ : 4 ≤ ρ) :
    (-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat (eta2rho ρ) δ =
      ((log ρ - log 4 : ℝ) : ℂ) *
        ((-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ) +
      (-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat (eta2rho 4) δ := by
  have hc : Continuous (fun t : ℝ => e (-(t * δ))) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_e_neg_mul δ t).continuousAt)
  have i2 : Integrable (fun t : ℝ => e (-(t * δ)) * (eta2 t : ℂ)) :=
    eta2_integrable.ofReal.bdd_mul hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => (norm_e _).le))
  have i4 : Integrable (fun t : ℝ => e (-(t * δ)) * (eta2rho 4 t : ℂ)) :=
    (eta2rho_integrable (by norm_num : (0 : ℝ) < 4)).ofReal.bdd_mul
      hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => (norm_e _).le))
  have heq : (fun t : ℝ => e (-(t * δ)) * (eta2rho ρ t : ℂ)) =
      (fun t : ℝ => ((log ρ - log 4 : ℝ) : ℂ) * (e (-(t * δ)) * (eta2 t : ℂ))) +
      (fun t : ℝ => e (-(t * δ)) * (eta2rho 4 t : ℂ)) := by
    funext t
    rw [weight_affine ρ t hρ]
    simp only [Pi.add_apply, Complex.ofReal_add, Complex.ofReal_mul]
    ring
  unfold fhat
  rw [heq, integral_add' (i2.const_mul ((log ρ - log 4 : ℝ) : ℂ)) i4, integral_const_mul]
  ring

/-- LEAF. Derived anchor for page 76 Lemma A.5 from the piecewise derivative at rho = 4. -/
theorem anchor_bound (δ : ℝ) :
    ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat (eta2rho 4) δ‖ ≤ 24 * log 4 := by
  let dL : ℝ → ℝ := fun t => 4 * ((2 - log (16 * t ^ 2)) / t ^ 2)
  let dR : ℝ → ℝ := fun t => -4 * ((2 - log (4 * t ^ 2)) / t ^ 2)
  have hl4 : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
  have hl42 : log (4 : ℝ) < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num at *
    nlinarith [log_two_lt_d9]
  have hdL (t : ℝ) (ht : 0 < t) : HasDerivAt (gL 4) (dL t) t := by
    convert (Kf_hasDerivAt (c := 16) (by norm_num) ht).const_mul 4 using 1
    funext y
    norm_num [gL]
  have hdR (t : ℝ) (ht : 0 < t) : HasDerivAt (gR 4) (dR t) t := by
    convert (Kf_hasDerivAt (c := 4) (by norm_num) ht).const_mul (-4) using 1
    funext y
    norm_num [gR]
  have hcont (c a b : ℝ) (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
      ContinuousOn (fun t : ℝ => (2 - log (c * t ^ 2)) / t ^ 2) (uIcc a b) := by
    have hn : ∀ t ∈ uIcc a b, t ≠ 0 := by
      intro t ht
      rw [uIcc_of_le hab] at ht
      linarith [ht.1]
    exact (continuousOn_const.sub
      ((continuousOn_const.mul (continuousOn_id.pow 2)).log
        (fun t ht => mul_ne_zero hc.ne' (pow_ne_zero _ (hn t ht))))).div
          (continuousOn_id.pow 2) (fun t ht => pow_ne_zero _ (hn t ht))
  have cL : ContinuousOn dL (uIcc (1 / 4 : ℝ) (1 / 2)) :=
    (hcont 16 (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)).const_mul 4
  have cR : ContinuousOn dR (uIcc (1 / 2 : ℝ) 1) :=
    (hcont 4 (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)).const_mul (-4)
  have signL : ∀ t ∈ Icc (1 / 4 : ℝ) (1 / 2), 0 ≤ dL t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlog := log_le_log (by positivity : 0 < 16 * t ^ 2)
      (by nlinarith [ht.1, ht.2, sq_nonneg (t - 1 / 2)] : 16 * t ^ 2 ≤ 4)
    dsimp [dL]
    exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (sq_nonneg _))
  have signR : ∀ t ∈ Icc (1 / 2 : ℝ) 1, dR t ≤ 0 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlog := log_le_log (by positivity : 0 < 4 * t ^ 2)
      (by nlinarith [ht.1, ht.2, sq_nonneg (t - 1)] : 4 * t ^ 2 ≤ 4)
    dsimp [dR]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (div_nonneg (by linarith) (sq_nonneg _))
  have eqL : (∫ t in (1 / 4 : ℝ)..(1 / 2), |dL t|) = 8 * log 4 := by
    rw [intervalIntegral.integral_congr (fun t ht =>
      abs_of_nonneg (signL t (by simpa only [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] using ht)))]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
      (gL_continuousOn (by norm_num : (0 : ℝ) < 4))
      (fun t ht => hdL t (by linarith [ht.1])) cL.intervalIntegrable]
    rw [gL_half, gL_quarter]
    norm_num
  have eqR : (∫ t in (1 / 2 : ℝ)..1, |dR t|) = 4 * log 4 := by
    rw [intervalIntegral.integral_congr (fun t ht =>
      abs_of_nonpos (signR t (by simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using ht))),
      intervalIntegral.integral_neg]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
      (gR_continuousOn (by norm_num : (0 : ℝ) < 4))
      (fun t ht => hdR t (by linarith [ht.1])) cR.intervalIntegrable]
    rw [gR_one, gR_half]
    norm_num
  have hL := norm_interval_fourier_mul_le (1 / 4) (1 / 2) δ (by norm_num)
    (gL 4) dL (by simpa only [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] using
      gL_continuousOn (by norm_num : (0 : ℝ) < 4)) cL
    (fun t ht => hdL t (by norm_num at ht; linarith [ht.1]))
  have hR := norm_interval_fourier_mul_le (1 / 2) 1 δ (by norm_num)
    (gR 4) dR (by simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using
      gR_continuousOn (by norm_num : (0 : ℝ) < 4)) cR
    (fun t ht => hdR t (by norm_num at ht; linarith [ht.1]))
  rw [eqL, gL_half, gL_quarter] at hL
  rw [eqR, gR_one, gR_half] at hR
  norm_num [abs_of_nonneg hl4, abs_mul] at hL hR
  have hm := congrArg (fun z : ℂ => (-2 * π * Complex.I * (δ : ℂ)) * z)
    (mul_fhat_eta2rho_eq 4 δ (by norm_num))
  rw [← mul_assoc, ← pow_two, mul_neg, mul_add] at hm
  rw [hm, norm_neg]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul]
  have hc : ‖-2 * (π : ℂ) * Complex.I * (δ : ℂ)‖ = 2 * π * |δ| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  simp only [norm_mul] at hc
  rw [hc]
  linarith


/-- Lemma A.5 assembled from the anchor and Lemma A.2.
CONDITIONAL ON the compact numerical leaf until its certificate is proved. -/
theorem lemmaA5_of_compact
    (hCompact : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 655 →
      ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ ≤ 31.521) : LemmaA5 := by
  intro ρ hρ δ
  have hc : 0 ≤ log ρ - log 4 :=
    sub_nonneg.mpr (Real.log_le_log (by norm_num) hρ)
  have h4 : 0 < log (4 : ℝ) := Real.log_pos (by norm_num)
  have hu := norm_second_fourier_eta2_le_of_nonneg_compact hCompact δ
  rw [fourier_affine ρ δ hρ]
  calc
    _ ≤ ‖((log ρ - log 4 : ℝ) : ℂ) *
        ((-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ)‖ +
        ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat (eta2rho 4) δ‖ := norm_add_le _ _
    _ = (log ρ - log 4) *
        ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ +
        ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat (eta2rho 4) δ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ (log ρ - log 4) * 31.521 + 24 * log 4 :=
      add_le_add (mul_le_mul_of_nonneg_left hu hc) (anchor_bound δ)
    _ < _ := by nlinarith

/-- The cited Lemma A.5 assembled from its leaves.
CONDITIONAL ON the compact numerical leaf. -/
theorem lemmaA5_assembled : LemmaA5 := lemmaA5_of_compact a2_compact

end LeanLab.HelfgottArcs.Decomp119b
