import Mathlib
import LeanLab.RamareSaouter2003.Decomp563b
import LeanLab.RamareSaouter2003.Decomp579c

/-!
Backlund pp. 364 and 365, displays 60 through 68.
Independent refinement of the sealed normalizer lower leaf.
AI wrote the Lean code. Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp579a
open Real Complex Set

/-- Backlund p. 363 display 57. Identical numeric factor to the sealed file. -/
noncomputable def normalizer (s : ℂ) : ℂ :=
  (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
    Complex.sqrt (Complex.sin (π * s / 2)) / Complex.log (-s * I)

/-- LEAF. Backlund p. 364 displays 60 and 61.
Lindelof pp. 97 through 99 displays 1, 3 and 5 give the real Stirling remainder.
Only the Gamma factor occurs in this two-sided relative norm estimate. -/
theorem gamma_relative (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    let G := Real.sqrt (2 * π) * (t / 2) ^ ((σ - 1) / 2) * Real.exp (-π * t / 4)
    G * (1 - 1 / t ^ 2) ≤ ‖Complex.Gamma (((σ : ℂ) + t * I) / 2)‖ ∧
    ‖Complex.Gamma (((σ : ℂ) + t * I) / 2)‖ ≤ G * (1 + 1 / t ^ 2) := by
  exact Decomp579c.gamma_relative σ t hσ ht

/-- Backlund p. 365 display 63, the norm of the principal square root.
This is Mathlib norm_cpow_inv_nat at degree two. -/
theorem cnorm_sqrt (z : ℂ) : ‖Complex.sqrt z‖ = Real.sqrt ‖z‖ := by
  simpa [Complex.sqrt, Real.sqrt_eq_rpow] using Complex.norm_cpow_inv_nat z 2

/-- LEAF. Backlund p. 365 displays 63 and 64.
Only the square root of sine occurs in this two-sided relative estimate. -/
theorem sine_relative (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    let S := Real.exp (π * t / 4) / Real.sqrt 2
    S * (1 - 1 / t ^ 2) ≤ ‖Complex.sqrt (Complex.sin (π * ((σ : ℂ) + t * I) / 2))‖ ∧
    ‖Complex.sqrt (Complex.sin (π * ((σ : ℂ) + t * I) / 2))‖ ≤ S * (1 + 1 / t ^ 2) := by
  let z : ℂ := π * ((σ : ℂ) + t * I) / 2
  let E := Real.exp (π * t / 2)
  let q := Real.exp (-π * t)
  let u := 1 / t ^ 2
  have htpos : 0 < t := by linarith
  have hE : 0 < E := Real.exp_pos _
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 / 2500 := by
    dsimp [u]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2500)
    nlinarith
  have hq : q ≤ u := by
    have h := Decomp563b.exp_cosine_error t ht
    dsimp [q, u]
    calc Real.exp (-π * t) ≤ 1 / (16 * t ^ 2) := h
      _ ≤ 1 / t ^ 2 := by
        apply one_div_le_one_div_of_le (by positivity : 0 < t ^ 2)
        nlinarith [sq_nonneg t]
  have hpos : (-z * I).re = π * t / 2 := by simp [z]
  have hneg : (z * I).re = -(π * t / 2) := by simp [z]
  have he : Real.exp (-(π * t / 2)) = E * q := by
    dsimp [E, q]
    rw [← Real.exp_add]
    congr 1
    ring
  have hupper := norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))
  have hlower := norm_sub_norm_le (Complex.exp (-z * I)) (Complex.exp (z * I))
  rw [Complex.norm_exp, Complex.norm_exp, hpos, hneg, he] at hupper hlower
  have hsin : ‖Complex.sin z‖ = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2 := by
    rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
    norm_num
  have hsup : ‖Complex.sin z‖ ≤ E / 2 * (1 + u) := by
    rw [hsin]
    nlinarith [mul_le_mul_of_nonneg_left hq hE.le]
  have hslo : E / 2 * (1 - u) ≤ ‖Complex.sin z‖ := by
    rw [hsin]
    nlinarith [mul_le_mul_of_nonneg_left hq hE.le]
  let S := Real.exp (π * t / 4) / Real.sqrt 2
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hSsq : S ^ 2 = E / 2 := by
    dsimp [S, E]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← Real.exp_nat_mul]
    congr 2
    norm_num
    ring
  have hrootsq : ‖Complex.sqrt (Complex.sin z)‖ ^ 2 = ‖Complex.sin z‖ := by
    rw [cnorm_sqrt, Real.sq_sqrt (norm_nonneg _)]
  change S * (1 - u) ≤ ‖Complex.sqrt (Complex.sin z)‖ ∧
    ‖Complex.sqrt (Complex.sin z)‖ ≤ S * (1 + u)
  constructor
  · have hsmall : (1 - u) ^ 2 ≤ 1 - u := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsmall (sq_nonneg S)
    rw [hSsq] at h
    have hnonneg : 0 ≤ S * (1 - u) := mul_nonneg hSpos.le (by linarith)
    nlinarith [norm_nonneg (Complex.sqrt (Complex.sin z))]
  · have hlarge : 1 + u ≤ (1 + u) ^ 2 := by nlinarith [sq_nonneg u]
    have h := mul_le_mul_of_nonneg_left hlarge (sq_nonneg S)
    rw [hSsq] at h
    have hnonneg : 0 ≤ S * (1 + u) := mul_nonneg hSpos.le (by linarith)
    nlinarith [norm_nonneg (Complex.sqrt (Complex.sin z))]


/-- LEAF. Backlund p. 365 displays 65 and 66.
Only the logarithm occurs. Its lower estimate uses its real part. -/
theorem logarithm_relative (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    Real.log t ≤ ‖Complex.log (-((σ : ℂ) + t * I) * I)‖ ∧
    ‖Complex.log (-((σ : ℂ) + t * I) * I)‖ ≤ Real.log t * (1 + 1 / t ^ 2) := by
  let z : ℂ := (t : ℂ) - (σ : ℂ) * I
  have hzre : z.re = t := by simp [z]
  have hzim : z.im = -σ := by simp [z]
  have htpos : 0 < t := by linarith
  have htne : t ≠ 0 := htpos.ne'
  have harg : -((σ : ℂ) + t * I) * I = z := by
    dsimp [z]
    simp only [neg_mul, add_mul, mul_assoc, Complex.I_mul_I]
    ring
  rw [harg]
  have hnorm : t ≤ ‖z‖ := by simpa [hzre] using Complex.re_le_norm z
  have hnormpos : 0 < ‖z‖ := htpos.trans_le hnorm
  have hlog : 3 ≤ Real.log t := by
    have he : Real.exp (3 : ℝ) < 50 := by
      have h := Real.exp_one_lt_three
      have h3 : Real.exp (3 : ℝ) = Real.exp 1 ^ 3 := by
        rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      rw [h3]
      have hcube := pow_lt_pow_left₀ h (Real.exp_pos 1).le (by decide : (3 : ℕ) ≠ 0)
      norm_num at hcube
      linarith
    have h := Real.log_le_log (Real.exp_pos 3) (he.le.trans ht)
    simpa using h
  have hlower : Real.log t ≤ (Complex.log z).re := by
    rw [Complex.log_re]
    exact Real.log_le_log htpos hnorm
  refine ⟨hlower.trans (Complex.re_le_norm _), ?_⟩
  have hsq : ‖z‖ ^ 2 = t ^ 2 + σ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    ring
  have hσsq : σ ^ 2 ≤ 1 := by nlinarith [hσ.1, hσ.2]
  have hnormup : ‖z‖ ≤ t + 1 / (2 * t) := by
    have he : 2 * t * (1 / (2 * t)) = 1 := by field_simp
    have hn : 0 ≤ 1 / (2 * t) := by positivity
    nlinarith [sq_nonneg (1 / (2 * t)), norm_nonneg z]
  have hreal : (Complex.log z).re ≤ Real.log t + 1 / (2 * t ^ 2) := by
    have hrat : ‖z‖ / t ≤ 1 + 1 / (2 * t ^ 2) := by
      rw [div_le_iff₀ htpos]
      convert hnormup using 1 <;> field_simp <;> ring
    have htaylor := Real.log_le_sub_one_of_pos (div_pos hnormpos htpos)
    rw [Real.log_div hnormpos.ne' htne] at htaylor
    rw [Complex.log_re]
    linarith
  have hargsmall : |z.arg| ≤ 1 / t := by
    have ha : |z.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rwa [hzre]))
    have harctan : Real.arctan (z.im / z.re) = z.arg := by
      rw [← Complex.tan_arg]
      exact Real.arctan_tan (abs_lt.mp ha).1 (abs_lt.mp ha).2
    rw [← harctan]
    calc |Real.arctan (z.im / z.re)| ≤ |z.im / z.re| := Real.abs_arctan_le_abs
      _ = σ / t := by rw [hzre, hzim, abs_div, abs_neg, abs_of_nonneg hσ.1, abs_of_pos htpos]
      _ ≤ 1 / t := div_le_div_of_nonneg_right hσ.2 htpos.le
  have him : (Complex.log z).im ^ 2 ≤ (1 / t) ^ 2 := by
    rw [Complex.log_im]
    exact sq_le_sq.mpr (by simpa [abs_of_pos htpos] using hargsmall)
  have hlognorm : ‖Complex.log z‖ ^ 2 = (Complex.log z).re ^ 2 + (Complex.log z).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hrpos : 0 ≤ (Complex.log z).re := by linarith
  have hreal2 : (Complex.log z).re ^ 2 ≤ (Real.log t + 1 / (2 * t ^ 2)) ^ 2 := by
    nlinarith
  have hu : 0 < 1 / t ^ 2 := by positivity
  have hid : (1 / t) ^ 2 = 1 / t ^ 2 := by ring
  have hhalf : 1 / (2 * t ^ 2) = (1 / t ^ 2) / 2 := by ring
  rw [hid] at him
  rw [hhalf] at hreal2
  have hscalar : (Real.log t + (1 / t ^ 2) / 2) ^ 2 + 1 / t ^ 2 ≤
      (Real.log t * (1 + 1 / t ^ 2)) ^ 2 := by
    nlinarith [sq_nonneg (Real.log t - 3), sq_nonneg (1 / t ^ 2),
      mul_nonneg (show 0 ≤ Real.log t - 3 by linarith) hu.le,
      mul_nonneg (show 0 ≤ Real.log t ^ 2 - 1 by nlinarith) (sq_nonneg (1 / t ^ 2))]
  have htarget : 0 ≤ Real.log t * (1 + 1 / t ^ 2) := by positivity
  nlinarith [norm_nonneg (Complex.log z)]


/-- Backlund p. 365 display 68, scalar relative-error budget. -/
theorem lower_error_budget (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 2500) :
    1 - 4 * u ≤ (1 - u) ^ 2 / (1 + u) := by
  rw [le_div_iff₀ (by linarith : 0 < 1 + u)]
  nlinarith [sq_nonneg u]

/-- Backlund p. 365 display 68, upper relative-error budget. -/
theorem upper_error_budget (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 2500) :
    (1 + u) ^ 2 ≤ 1 + 4 * u := by
  nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]

/-- Backlund p. 365 displays 60, 62 and 63, cancellation of leading factors. -/
theorem leading_factors (σ t : ℝ) (ht : 0 < t) :
    π ^ (-σ / 2) *
      (Real.sqrt (2 * π) * (t / 2) ^ ((σ - 1) / 2) * Real.exp (-π * t / 4)) *
      (Real.exp (π * t / 4) / Real.sqrt 2) =
        (t / (2 * π)) ^ ((σ - 1) / 2) := by
  have he : Real.exp (-π * t / 4) * Real.exp (π * t / 4) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  have hs : Real.sqrt (2 * π) / Real.sqrt 2 = π ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_div_cancel_left₀ _
      (by positivity : Real.sqrt (2 : ℝ) ≠ 0), Real.sqrt_eq_rpow]
  calc
    _ = (π ^ (-σ / 2) * (Real.sqrt (2 * π) / Real.sqrt 2)) *
        (t / 2) ^ ((σ - 1) / 2) *
        (Real.exp (-π * t / 4) * Real.exp (π * t / 4)) := by ring
    _ = π ^ (-(σ - 1) / 2) * (t / 2) ^ ((σ - 1) / 2) := by
      rw [he, mul_one, hs, ← Real.rpow_add Real.pi_pos]
      congr 2 <;> ring
    _ = ((t / 2) / π) ^ ((σ - 1) / 2) := by
      rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ t / 2) Real.pi_pos.le,
        show -(σ - 1) / 2 = -((σ - 1) / 2) by ring,
        Real.rpow_neg Real.pi_pos.le]
      ring
    _ = _ := by congr 1; ring

/-- Backlund p. 365 display 67, lower normalizer estimate from the factor leaves.
CONDITIONAL ON gamma_relative, sine_relative and logarithm_relative. -/
theorem normalizer_relative_lower (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (ht : 50 ≤ t) :
    (t / (2 * π)) ^ ((σ - 1) / 2) / Real.log t * (1 - 4 / t ^ 2) ≤
      ‖normalizer ((σ : ℂ) + t * I)‖ := by
  let G := Real.sqrt (2 * π) * (t / 2) ^ ((σ - 1) / 2) * Real.exp (-π * t / 4)
  let S := Real.exp (π * t / 4) / Real.sqrt 2
  let u := 1 / t ^ 2
  have htpos : 0 < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 / 2500 := by
    dsimp [u]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2500)
    nlinarith
  have h1u : 0 ≤ 1 - u := by linarith
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hg := (gamma_relative σ t hσ ht).1
  have hs := (sine_relative σ t hσ ht).1
  have hl := logarithm_relative σ t hσ ht
  change G * (1 - u) ≤ _ at hg
  change S * (1 - u) ≤ _ at hs
  have hpi : ‖(π : ℂ) ^ (-((σ : ℂ) + t * I) / 2)‖ = π ^ (-σ / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hp : 0 ≤ π ^ (-σ / 2) := Real.rpow_nonneg Real.pi_pos.le _
  have hprod := mul_le_mul hg hs (mul_nonneg hS h1u) (norm_nonneg _)
  have hnum := mul_le_mul_of_nonneg_left hprod hp
  have hden : 0 < ‖Complex.log (-((σ : ℂ) + t * I) * I)‖ := hlog.trans_le hl.1
  have hdiv := div_le_div₀ (mul_nonneg hp (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    hnum hden hl.2
  have hscale : π ^ (-σ / 2) * G * S = (t / (2 * π)) ^ ((σ - 1) / 2) :=
    leading_factors σ t htpos
  have hbound : (t / (2 * π)) ^ ((σ - 1) / 2) / Real.log t *
      ((1 - u) ^ 2 / (1 + u)) ≤ ‖normalizer ((σ : ℂ) + t * I)‖ := by
    rw [normalizer, norm_div, norm_mul, norm_mul, hpi]
    convert hdiv using 1
    · rw [← hscale]; dsimp [u]
      field_simp
      <;> ring
    · ring
  have herr := mul_le_mul_of_nonneg_left (lower_error_budget u hu0 hu1)
    (show 0 ≤ (t / (2 * π)) ^ ((σ - 1) / 2) / Real.log t by positivity)
  convert herr.trans hbound using 1 <;> dsimp [u] <;> ring

/-- Backlund p. 365 display 68, exact lower leaf assembled from smaller factors.
CONDITIONAL ON the factor leaves. The theorem has no admission of its own. -/
theorem normalizer_lower (σ t : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    1 ≤ ‖normalizer ((σ : ℂ) + t * I)‖ *
      (t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t) := by
  have htpos : 0 < t := by linarith
  have hd : 0 < t ^ 2 - 4 := by nlinarith
  have htne : t ≠ 0 := htpos.ne'
  have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith : 1 < t)).ne'
  have hb : 0 < t / (2 * π) := by positivity
  have hr : (t / (2 * π)) ^ ((σ - 1) / 2) *
      (t / (2 * π)) ^ ((1 - σ) / 2) = 1 := by
    rw [← Real.rpow_add hb]
    convert Real.rpow_zero (t / (2 * π)) using 1 <;> congr 1 <;> ring
  have hm : 0 ≤ t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t := by
    apply mul_nonneg _ (Real.log_nonneg (by linarith))
    positivity
  have h := mul_le_mul_of_nonneg_right (normalizer_relative_lower σ t hσ ht) hm
  have he : ((t / (2 * π)) ^ ((σ - 1) / 2) / Real.log t * (1 - 4 / t ^ 2)) *
      (t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t) = 1 := by
    field_simp
    nlinarith [hr]
  rwa [he] at h

end LeanLab.RamareSaouter2003.Decomp579a

#print axioms LeanLab.RamareSaouter2003.Decomp579a.lower_error_budget
#print axioms LeanLab.RamareSaouter2003.Decomp579a.upper_error_budget

#print axioms LeanLab.RamareSaouter2003.Decomp579a.gamma_relative
#print axioms LeanLab.RamareSaouter2003.Decomp579a.cnorm_sqrt
#print axioms LeanLab.RamareSaouter2003.Decomp579a.sine_relative
#print axioms LeanLab.RamareSaouter2003.Decomp579a.logarithm_relative
#print axioms LeanLab.RamareSaouter2003.Decomp579a.leading_factors
#print axioms LeanLab.RamareSaouter2003.Decomp579a.normalizer_relative_lower
#print axioms LeanLab.RamareSaouter2003.Decomp579a.normalizer_lower
