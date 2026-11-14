import Mathlib
import LeanLab.PNTPort.ZetaZeros.Count

/-!
Backlund pp. 363 through 368 displays 57 through 73.
The normalized boundary estimates and the half-strip principle are distinct.
No target file or descendant is imported.
AI wrote the Lean code. Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp563c
open Real Complex Set Filter Metric MeasureTheory
open scoped Topology

/-- Backlund p. 363 display 57, the factor multiplying the actual zeta function. -/
noncomputable def normalizer (s : ℂ) : ℂ :=
  (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
    Complex.sqrt (Complex.sin (π * s / 2)) / Complex.log (-s * I)

private lemma cnorm_sqrt (z : ℂ) : ‖Complex.sqrt z‖ = Real.sqrt ‖z‖ := by
  rcases eq_or_ne z 0 with hz | hz
  · subst hz; simp
  · rw [sqrt_eq_exp hz, Complex.norm_exp]
    have hre : (Complex.log z / 2).re = Real.log ‖z‖ / 2 := by
      rw [Complex.div_re]
      simp [Complex.log_re]
      ring
    rw [hre, show Real.log ‖z‖ / 2 = Real.log ‖z‖ * (1 / 2) by ring, Real.exp_mul,
      Real.exp_log (by positivity), Real.sqrt_eq_rpow]

private lemma mul_I_mul_I (x : ℂ) : x * I * I = -x := by
  rw [mul_assoc, Complex.I_mul_I]; ring

private lemma neg_mul_I_I (t : ℝ) : -((t : ℂ) * I) * I = (t : ℂ) := by
  rw [neg_mul, mul_I_mul_I]; ring

private lemma neg_one_add_mul_I (t : ℝ) :
    -((1 : ℂ) + (t : ℂ) * I) * I = (t : ℂ) - I := by
  have h : ((1 : ℂ) + (t : ℂ) * I) * I = I - (t : ℂ) := by
    rw [add_mul, one_mul, mul_assoc, Complex.I_mul_I]; ring
  rw [neg_mul, h]; ring

private lemma cnorm_sin_mul_I (y : ℝ) (hy : 0 < y) :
    ‖Complex.sin ((y : ℂ) * I)‖ = Real.sinh y := by
  rw [Complex.sin_mul_I, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sinh,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- `‖Γ(i y)‖² * y = π / sinh (π y)`. -/
private lemma Gamma_I_norm_sq (y : ℝ) (hy : 0 < y) :
    ‖Complex.Gamma ((y : ℂ) * I)‖ ^ 2 * y = π / Real.sinh (π * y) := by
  have hyne : ((y : ℂ) * I) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hconj2 : -((y : ℂ) * I) = (starRingEnd ℂ) ((y : ℂ) * I) := by
    apply Complex.ext <;> simp
  have hrefl : ‖Complex.Gamma ((y : ℂ) * I)‖ * ‖Complex.Gamma (1 - (y : ℂ) * I)‖ =
      π / ‖Complex.sin (π * ((y : ℂ) * I))‖ := by
    have h := Complex.Gamma_mul_Gamma_one_sub ((y : ℂ) * I)
    calc ‖Complex.Gamma ((y : ℂ) * I)‖ * ‖Complex.Gamma (1 - (y : ℂ) * I)‖
        = ‖Complex.Gamma ((y : ℂ) * I) * Complex.Gamma (1 - (y : ℂ) * I)‖ :=
          (norm_mul _ _).symm
      _ = ‖π / Complex.sin (π * ((y : ℂ) * I))‖ := by rw [h]
      _ = π / ‖Complex.sin (π * ((y : ℂ) * I))‖ := by simp
  have hstep : ‖Complex.Gamma (1 - (y : ℂ) * I)‖ = y * ‖Complex.Gamma ((y : ℂ) * I)‖ := by
    have hne : -((y : ℂ) * I) ≠ 0 := by simpa using hyne
    have hadd := Complex.Gamma_add_one (-((y : ℂ) * I)) hne
    have he : -((y : ℂ) * I) + 1 = 1 - (y : ℂ) * I := by ring
    rw [he] at hadd
    rw [hadd, norm_mul]
    have h2 : ‖-((y : ℂ) * I)‖ = y := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy,
        Complex.norm_I, mul_one]
    have h3 : ‖Complex.Gamma (-((y : ℂ) * I))‖ = ‖Complex.Gamma ((y : ℂ) * I)‖ := by
      rw [hconj2, Complex.Gamma_conj, Complex.norm_conj]
    rw [h2, h3]
  have hsin : ‖Complex.sin (π * ((y : ℂ) * I))‖ = Real.sinh (π * y) := by
    have he : π * ((y : ℂ) * I) = (((π * y : ℝ)) : ℂ) * I := by push_cast; ring
    rw [he]
    exact cnorm_sin_mul_I (π * y) (by positivity)
  calc ‖Complex.Gamma ((y : ℂ) * I)‖ ^ 2 * y
      = ‖Complex.Gamma ((y : ℂ) * I)‖ * (y * ‖Complex.Gamma ((y : ℂ) * I)‖) := by ring
    _ = ‖Complex.Gamma ((y : ℂ) * I)‖ * ‖Complex.Gamma (1 - (y : ℂ) * I)‖ := by rw [hstep]
    _ = π / ‖Complex.sin (π * ((y : ℂ) * I))‖ := hrefl
    _ = π / Real.sinh (π * y) := by rw [hsin]

/-- `‖Γ(1 + i y)‖² = π y / sinh (π y)`. -/
private lemma Gamma_one_add_I_norm_sq (y : ℝ) (hy : 0 < y) :
    ‖Complex.Gamma (1 + (y : ℂ) * I)‖ ^ 2 = π * y / Real.sinh (π * y) := by
  have hbase := Gamma_I_norm_sq y hy
  have hyne : ((y : ℂ) * I) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hadd := Complex.Gamma_add_one ((y : ℂ) * I) hyne
  have he : (y : ℂ) * I + 1 = 1 + (y : ℂ) * I := by ring
  rw [he] at hadd
  have hnorm : ‖((y : ℂ) * I)‖ = y := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy, Complex.norm_I, mul_one]
  rw [hadd, norm_mul, hnorm, mul_pow]
  have hs0 : Real.sinh (π * y) ≠ 0 := (by positivity : 0 < Real.sinh (π * y)).ne'
  rw [show ‖Complex.Gamma ((y : ℂ) * I)‖ ^ 2 = π / Real.sinh (π * y) / y from by
    rw [eq_div_iff hy.ne']
    exact hbase]
  field_simp

/-- `‖Γ(1/2 + i y)‖² = π / cosh (π y)`. -/
private lemma Gamma_half_I_norm_sq (y : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ ^ 2 = π / Real.cosh (π * y) := by
  have hconj2 : 1 - ((1 / 2 : ℂ) + (y : ℂ) * I) =
      (starRingEnd ℂ) ((1 / 2 : ℂ) + (y : ℂ) * I) := by
    apply Complex.ext <;> simp <;> norm_num
  have hnorm : ‖Complex.Gamma (1 - ((1 / 2 : ℂ) + (y : ℂ) * I))‖ =
      ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ := by
    rw [hconj2, Complex.Gamma_conj, Complex.norm_conj]
  have hrefl : ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ *
      ‖Complex.Gamma (1 - ((1 / 2 : ℂ) + (y : ℂ) * I))‖ =
      π / ‖Complex.sin (π * ((1 / 2 : ℂ) + (y : ℂ) * I))‖ := by
    have h := Complex.Gamma_mul_Gamma_one_sub ((1 / 2 : ℂ) + (y : ℂ) * I)
    calc ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ *
          ‖Complex.Gamma (1 - ((1 / 2 : ℂ) + (y : ℂ) * I))‖
        = ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I) *
            Complex.Gamma (1 - ((1 / 2 : ℂ) + (y : ℂ) * I))‖ := (norm_mul _ _).symm
      _ = ‖π / Complex.sin (π * ((1 / 2 : ℂ) + (y : ℂ) * I))‖ := by rw [h]
      _ = π / ‖Complex.sin (π * ((1 / 2 : ℂ) + (y : ℂ) * I))‖ := by simp
  have hsin : Complex.sin (π * ((1 / 2 : ℂ) + (y : ℂ) * I)) =
      ((Real.cosh (π * y) : ℝ) : ℂ) := by
    have he : π * ((1 / 2 : ℂ) + (y : ℂ) * I) =
        ((π / 2 : ℝ) : ℂ) + (((π * y : ℝ)) : ℂ) * I := by push_cast; ring
    rw [he, Complex.sin_add_mul_I]
    have h1 : Complex.sin (((π / 2 : ℝ)) : ℂ) = 1 := by
      rw [← Complex.ofReal_sin]; norm_num
    have h2 : Complex.cos (((π / 2 : ℝ)) : ℂ) = 0 := by
      rw [← Complex.ofReal_cos]; norm_num
    rw [h1, h2]
    simp only [one_mul, zero_mul, add_zero]
    rw [← Complex.ofReal_cosh]
  calc ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ ^ 2
      = ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ *
        ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ := by ring
    _ = ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ *
        ‖Complex.Gamma (1 - ((1 / 2 : ℂ) + (y : ℂ) * I))‖ := by rw [hnorm]
    _ = π / ‖Complex.sin (π * ((1 / 2 : ℂ) + (y : ℂ) * I))‖ := hrefl
    _ = π / Real.cosh (π * y) := by
      rw [hsin, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

private lemma Gamma_one_sub_I_norm (y : ℝ) :
    ‖Complex.Gamma (1 - (y : ℂ) * I)‖ = ‖Complex.Gamma (1 + (y : ℂ) * I)‖ := by
  have hconj2 : 1 - (y : ℂ) * I = (starRingEnd ℂ) (1 + (y : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [hconj2, Complex.Gamma_conj, Complex.norm_conj]

private lemma cnorm_cos_half (t : ℝ) (ht : 0 < t) :
    ‖Complex.cos (π * (1 - (t : ℂ) * I) / 2)‖ = Real.sinh (π * t / 2) := by
  have h1 : Complex.cos (((π / 2 : ℝ)) : ℂ) = 0 := by
    rw [← Complex.ofReal_cos]; norm_num
  have h2 : Complex.sin (((π / 2 : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_sin]; norm_num
  have h3 : Complex.sinh ((-(π * t / 2) : ℝ) : ℂ) = -(((Real.sinh (π * t / 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sinh, show Real.sinh (-(π * t / 2)) = -Real.sinh (π * t / 2) by
      rw [Real.sinh_neg]]
    push_cast
    ring
  have he : π * (1 - (t : ℂ) * I) / 2 =
      ((π / 2 : ℝ) : ℂ) + ((-(π * t / 2) : ℝ) : ℂ) * I := by push_cast; ring
  rw [he, Complex.cos_add_mul_I, h1, h2, h3]
  simp only [zero_mul, one_mul, zero_sub, norm_neg, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one]
  exact abs_of_pos (by positivity)

/-- LEAF. Backlund pp. 365 and 366 displays 67 through 72.
The right boundary saving and functional symmetry control both vertical edges.
Only boundary points of the normalized function occur here. -/
theorem normalized_vertical_boundary
    (h54 : ∀ σ t : ℝ, 1 ≤ σ → 50 ≤ t →
      ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ Real.log t - 0.048)
    (t : ℝ) (ht : 50 ≤ t) :
    ‖normalizer (t * I) * riemannZeta (t * I)‖ ≤ 1 ∧
    ‖normalizer (1 + t * I) * riemannZeta (1 + t * I)‖ ≤ 1 := by

  have htpos : 0 < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hlog48 : (0.048 : ℝ) < Real.log t := by
    have h50 : (0.048 : ℝ) < Real.log 50 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      calc Real.exp 0.048 < Real.exp 1 := by gcongr <;> norm_num
        _ < 3 := Real.exp_one_lt_three
        _ < 50 := by norm_num
    have := Real.log_le_log (by norm_num : (0:ℝ) < 50) ht
    linarith
  have hSpos : 0 < Real.sinh (π * (t / 2)) := by positivity
  have hCpos : 0 < Real.cosh (π * (t / 2)) := by positivity
  have hEpos : 0 < Real.exp (π * t / 2) := Real.exp_pos _
  have htne : t ≠ 0 := htpos.ne'
  have hSne : Real.sinh (π * (t / 2)) ≠ 0 := hSpos.ne'
  have hSpos2 : 0 < Real.sinh (π * t / 2) := by positivity
  have hSne2 : Real.sinh (π * t / 2) ≠ 0 := hSpos2.ne'
  have hCpos2 : 0 < Real.cosh (π * t / 2) := by positivity
  have hSC : Real.sinh (π * t / 2) ≤ Real.cosh (π * t / 2) :=
    le_of_lt (Real.sinh_lt_cosh (π * t / 2))
  have hSt : 0 < Real.sinh (π * t) := by positivity
  have hStne : Real.sinh (π * t) ≠ 0 := hSt.ne'

  have hN1 : ‖normalizer ((t : ℂ) * I)‖ = Real.sqrt (2 * π / t) / Real.log t := by
    have hexp : (-((t : ℂ) * I) / 2 : ℂ).re = 0 := by simp
    have hpi : ‖(π : ℂ) ^ (-((t : ℂ) * I) / 2)‖ = 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      rw [hexp]
      exact Real.rpow_zero π
    have harg : ((t : ℂ) * I) / 2 = ((t / 2 : ℝ) : ℂ) * I := by push_cast; ring
    have hb := Gamma_I_norm_sq (t / 2) (by linarith)
    have hsq : ‖Complex.Gamma (((t : ℂ) * I) / 2)‖ ^ 2 =
        π / (t / 2 * Real.sinh (π * (t / 2))) := by
      rw [harg]
      have hmul : t / 2 * Real.sinh (π * (t / 2)) ≠ 0 :=
        mul_ne_zero (by linarith) hSne
      rw [eq_div_iff hmul]
      have hb2 : ‖Complex.Gamma ((((t / 2 : ℝ)) : ℂ) * I)‖ ^ 2 * (t / 2) *
          Real.sinh (π * (t / 2)) = π := by
        rw [hb]
        field_simp [hSne]
      rw [show ‖Complex.Gamma ((((t / 2 : ℝ)) : ℂ) * I)‖ ^ 2 *
          (t / 2 * Real.sinh (π * (t / 2)))
          = ‖Complex.Gamma ((((t / 2 : ℝ)) : ℂ) * I)‖ ^ 2 * (t / 2) *
            Real.sinh (π * (t / 2)) by ring]
      exact hb2
    have hG : ‖Complex.Gamma (((t : ℂ) * I) / 2)‖ =
        Real.sqrt (π / (t / 2 * Real.sinh (π * (t / 2)))) := by
      rw [← hsq]
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    have hs : ‖Complex.sqrt (Complex.sin (π * (((t : ℂ) * I)) / 2))‖ =
        Real.sqrt (Real.sinh (π * (t / 2))) := by
      rw [cnorm_sqrt]
      have hsinarg : π * (((t : ℂ) * I)) / 2 = (((π * (t / 2) : ℝ)) : ℂ) * I := by
        push_cast; ring
      rw [hsinarg, cnorm_sin_mul_I (π * (t / 2)) (by positivity)]
    have hlg : ‖Complex.log (-(((t : ℂ) * I)) * I)‖ = Real.log t := by
      rw [neg_mul_I_I, ← Complex.ofReal_log (le_of_lt htpos), Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hlogpos]
    have hnum : Real.sqrt (π / (t / 2 * Real.sinh (π * (t / 2)))) *
        Real.sqrt (Real.sinh (π * (t / 2))) = Real.sqrt (2 * π / t) := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ π / (t / 2 * Real.sinh (π * (t / 2))))]
      congr 1
      field_simp [htne, hSne]
    rw [normalizer, norm_div, norm_mul, norm_mul, hpi, hG, hs, hlg, one_mul, hnum]

  have hzeta : ‖riemannZeta ((t : ℂ) * I)‖ ≤
      2 * (2 * π)⁻¹ * Real.sqrt (π * t / Real.sinh (π * t)) * Real.sinh (π * t / 2) *
        (Real.log t - 0.048) := by
    have hsne : ∀ n : ℕ, (1 - (t : ℂ) * I) ≠ -(n : ℂ) := by
      intro n h
      have hi := congrArg Complex.im h
      simp at hi
      linarith
    have hsne1 : (1 - (t : ℂ) * I) ≠ 1 := by
      intro h
      have hi := congrArg Complex.im h
      simp at hi
      linarith
    have hFE := riemannZeta_one_sub (s := 1 - (t : ℂ) * I) hsne hsne1
    have h1s : 1 - (1 - (t : ℂ) * I) = (t : ℂ) * I := by ring
    rw [h1s] at hFE
    have hA : ‖(2 * (π : ℂ)) ^ (-(1 - (t : ℂ) * I))‖ = (2 * π)⁻¹ := by
      have hb : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
      rw [hb, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < 2 * π)]
      have hre : (-(1 - (t : ℂ) * I)).re = -(1 : ℝ) := by simp
      rw [hre]
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * π), Real.rpow_one]
    have hB : ‖Complex.Gamma (1 - (t : ℂ) * I)‖ =
        Real.sqrt (π * t / Real.sinh (π * t)) := by
      rw [Gamma_one_sub_I_norm]
      have hb := Gamma_one_add_I_norm_sq t htpos
      rw [← hb]
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    have hC := cnorm_cos_half t htpos
    have hD : ‖riemannZeta (1 - (t : ℂ) * I)‖ ≤ Real.log t - 0.048 := by
      have hconjz : 1 - (t : ℂ) * I = (starRingEnd ℂ) (1 + (t : ℂ) * I) := by
        apply Complex.ext <;> simp
      rw [hconjz, riemannZeta_conj, Complex.norm_conj]
      exact h54 1 t le_rfl ht
    rw [hFE]
    have h0 : (0:ℝ) ≤ Real.log t - 0.048 := by linarith
    calc ‖2 * (2 * (π : ℂ)) ^ (-(1 - (t : ℂ) * I)) * Complex.Gamma (1 - (t : ℂ) * I) *
          Complex.cos (π * (1 - (t : ℂ) * I) / 2) * riemannZeta (1 - (t : ℂ) * I)‖
        = 2 * ‖(2 * (π : ℂ)) ^ (-(1 - (t : ℂ) * I))‖ *
          ‖Complex.Gamma (1 - (t : ℂ) * I)‖ *
          ‖Complex.cos (π * (1 - (t : ℂ) * I) / 2)‖ *
          ‖riemannZeta (1 - (t : ℂ) * I)‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul]
          norm_num
      _ ≤ 2 * (2 * π)⁻¹ * Real.sqrt (π * t / Real.sinh (π * t)) *
          Real.sinh (π * t / 2) * (Real.log t - 0.048) := by
          rw [hA, hB, hC]
          gcongr

  have hkey : Real.sinh (π * t / 2) * Real.sqrt (2 / Real.sinh (π * t)) ≤ 1 := by
    have hsinh2 : Real.sinh (π * t) = 2 * Real.sinh (π * t / 2) * Real.cosh (π * t / 2) := by
      have he : π * t = π * t / 2 + π * t / 2 := by ring
      rw [he, Real.sinh_add]; ring
    have hcmp : Real.sinh (π * t / 2) ≤ Real.sqrt (Real.sinh (π * t) / 2) := by
      rw [← Real.sqrt_sq (le_of_lt hSpos2)]
      apply Real.sqrt_le_sqrt
      rw [hsinh2]
      nlinarith [hSpos2, hCpos2, hSC]
    have h5 : Real.sqrt (Real.sinh (π * t) / 2) * Real.sqrt (2 / Real.sinh (π * t)) = 1 := by
      rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ Real.sinh (π * t) / 2)]
      rw [show Real.sinh (π * t) / 2 * (2 / Real.sinh (π * t)) = 1 by field_simp [hStne]]
      exact Real.sqrt_one
    calc Real.sinh (π * t / 2) * Real.sqrt (2 / Real.sinh (π * t))
        ≤ Real.sqrt (Real.sinh (π * t) / 2) * Real.sqrt (2 / Real.sinh (π * t)) := by
          gcongr
      _ = 1 := h5
  have hmain : Real.sqrt (2 * π / t) * Real.sqrt (π * t / Real.sinh (π * t)) *
      Real.sinh (π * t / 2) ≤ π := by
    have e : Real.sqrt (2 * π / t) * Real.sqrt (π * t / Real.sinh (π * t)) =
        π * Real.sqrt (2 / Real.sinh (π * t)) := by
      rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * π / t)]
      rw [show 2 * π / t * (π * t / Real.sinh (π * t)) = π ^ 2 * (2 / Real.sinh (π * t)) by
        field_simp [hStne, htne]]
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ π ^ 2), Real.sqrt_sq (le_of_lt Real.pi_pos)]
    calc Real.sqrt (2 * π / t) * Real.sqrt (π * t / Real.sinh (π * t)) *
          Real.sinh (π * t / 2)
        = π * (Real.sinh (π * t / 2) * Real.sqrt (2 / Real.sinh (π * t))) := by rw [e]; ring
      _ ≤ π * 1 := mul_le_mul_of_nonneg_left hkey (le_of_lt Real.pi_pos)
      _ = π := by ring
  have hreal : Real.sqrt (2 * π / t) / Real.log t *
      (2 * (2 * π)⁻¹ * Real.sqrt (π * t / Real.sinh (π * t)) * Real.sinh (π * t / 2) *
        (Real.log t - 0.048)) ≤ 1 := by
    have hconst : 2 * (2 * π)⁻¹ = 1 / π := by field_simp
    rw [hconst]
    have hL : Real.log t ≠ 0 := hlogpos.ne'
    have hE : Real.sqrt (2 * π / t) / Real.log t *
        ((1 / π) * Real.sqrt (π * t / Real.sinh (π * t)) * Real.sinh (π * t / 2) *
          (Real.log t - 0.048))
        = ((1 / π) * (Real.sqrt (2 * π / t) * Real.sqrt (π * t / Real.sinh (π * t)) *
          Real.sinh (π * t / 2))) * ((Real.log t - 0.048) / Real.log t) := by
      field_simp [hL, htne, hSne]
    rw [hE]
    have hb1 : (1 / π) * (Real.sqrt (2 * π / t) * Real.sqrt (π * t / Real.sinh (π * t)) *
        Real.sinh (π * t / 2)) ≤ 1 := by
      calc (1 / π) * (Real.sqrt (2 * π / t) * Real.sqrt (π * t / Real.sinh (π * t)) *
            Real.sinh (π * t / 2))
          ≤ (1 / π) * π := mul_le_mul_of_nonneg_left hmain (by positivity)
        _ = 1 := by field_simp
    have hb2 : (Real.log t - 0.048) / Real.log t ≤ 1 := by
      rw [div_le_iff₀ hlogpos]
      linarith
    have hb3 : 0 ≤ (Real.log t - 0.048) / Real.log t :=
      div_nonneg (by linarith) (le_of_lt hlogpos)
    calc (1 / π) * (Real.sqrt (2 * π / t) * Real.sqrt (π * t / Real.sinh (π * t)) *
          Real.sinh (π * t / 2)) * ((Real.log t - 0.048) / Real.log t)
        ≤ 1 * 1 := mul_le_mul hb1 hb2 hb3 (by norm_num)
      _ = 1 := by norm_num
  constructor
  · calc ‖normalizer ((t : ℂ) * I) * riemannZeta ((t : ℂ) * I)‖
        = ‖normalizer ((t : ℂ) * I)‖ * ‖riemannZeta ((t : ℂ) * I)‖ := norm_mul _ _
      _ ≤ (Real.sqrt (2 * π / t) / Real.log t) *
          (2 * (2 * π)⁻¹ * Real.sqrt (π * t / Real.sinh (π * t)) * Real.sinh (π * t / 2) *
            (Real.log t - 0.048)) := by
          rw [hN1]
          exact mul_le_mul_of_nonneg_left hzeta (by positivity)
      _ ≤ 1 := hreal
  · have hN2 : ‖normalizer (1 + (t : ℂ) * I)‖ = 1 / ‖Complex.log ((t : ℂ) - I)‖ := by
      have hpi : ‖(π : ℂ) ^ (-((1 : ℂ) + (t : ℂ) * I) / 2)‖ = π ^ (-(1 / 2 : ℝ)) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
        norm_num
      have harg : ((1 : ℂ) + (t : ℂ) * I) / 2 =
          (1 / 2 : ℂ) + (((t / 2 : ℝ)) : ℂ) * I := by push_cast; ring
      have hG : ‖Complex.Gamma (((1 : ℂ) + (t : ℂ) * I) / 2)‖ =
          Real.sqrt (π / Real.cosh (π * (t / 2))) := by
        have hb := Gamma_half_I_norm_sq (t / 2)
        have hsq : ‖Complex.Gamma (((1 : ℂ) + (t : ℂ) * I) / 2)‖ ^ 2 =
            π / Real.cosh (π * (t / 2)) := by
          rw [harg]; exact hb
        rw [← hsq]
        exact (Real.sqrt_sq (norm_nonneg _)).symm
      have hs : ‖Complex.sqrt (Complex.sin (π * ((1 : ℂ) + (t : ℂ) * I) / 2))‖ =
          Real.sqrt (Real.cosh (π * (t / 2))) := by
        rw [cnorm_sqrt]
        have hsin : ‖Complex.sin (π * ((1 : ℂ) + (t : ℂ) * I) / 2)‖ = Real.cosh (π * (t / 2)) := by
          have he : π * ((1 : ℂ) + (t : ℂ) * I) / 2 =
              ((π / 2 : ℝ) : ℂ) + (((π * (t / 2) : ℝ)) : ℂ) * I := by push_cast; ring
          rw [he, Complex.sin_add_mul_I]
          have h1 : Complex.sin (((π / 2 : ℝ)) : ℂ) = 1 := by
            rw [← Complex.ofReal_sin]; norm_num
          have h2 : Complex.cos (((π / 2 : ℝ)) : ℂ) = 0 := by
            rw [← Complex.ofReal_cos]; norm_num
          rw [h1, h2]
          simp only [one_mul, zero_mul, add_zero]
          rw [← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity)]
        rw [hsin]
      have hlg : ‖Complex.log (-((1 : ℂ) + (t : ℂ) * I) * I)‖ = ‖Complex.log ((t : ℂ) - I)‖ := by
        rw [neg_one_add_mul_I]
      rw [normalizer, norm_div, norm_mul, norm_mul, hpi, hG, hs, hlg]
      have h1 : π ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt π := by
        rw [Real.rpow_neg (le_of_lt Real.pi_pos), Real.sqrt_eq_rpow]
        simp
      have h2 : Real.sqrt (π / Real.cosh (π * (t / 2))) *
          Real.sqrt (Real.cosh (π * (t / 2))) = Real.sqrt π := by
        rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ π / Real.cosh (π * (t / 2)))]
        rw [show π / Real.cosh (π * (t / 2)) * Real.cosh (π * (t / 2)) = π by field_simp]
      have h3 : 1 / Real.sqrt π * Real.sqrt π = 1 := by
        have hsp : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
        field_simp
      calc (π ^ (-(1 / 2 : ℝ)) * Real.sqrt (π / Real.cosh (π * (t / 2))) *
            Real.sqrt (Real.cosh (π * (t / 2)))) / ‖Complex.log ((t : ℂ) - I)‖
          = (1 / Real.sqrt π * (Real.sqrt (π / Real.cosh (π * (t / 2))) *
              Real.sqrt (Real.cosh (π * (t / 2))))) / ‖Complex.log ((t : ℂ) - I)‖ := by
            rw [h1]; ring_nf
        _ = (1 / Real.sqrt π * Real.sqrt π) / ‖Complex.log ((t : ℂ) - I)‖ := by rw [h2]
        _ = 1 / ‖Complex.log ((t : ℂ) - I)‖ := by rw [h3]
    have hlog : Real.log t ≤ ‖Complex.log ((t : ℂ) - I)‖ := by
      have hre : (Complex.log ((t : ℂ) - I)).re = Real.log ‖(t : ℂ) - I‖ := Complex.log_re _
      have hge : t ≤ ‖(t : ℂ) - I‖ := by
        have hn : ‖(t : ℂ) - I‖ ^ 2 = t ^ 2 + 1 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp
          ring
        nlinarith [hn, norm_nonneg ((t : ℂ) - I), htpos]
      have hl := Real.log_le_log htpos hge
      linarith [hre, hl, Complex.re_le_norm (Complex.log ((t : ℂ) - I))]
    have hlogpos' : 0 < ‖Complex.log ((t : ℂ) - I)‖ := lt_of_lt_of_le hlogpos hlog
    have hD2 : ‖riemannZeta (1 + (t : ℂ) * I)‖ ≤ Real.log t - 0.048 := h54 1 t le_rfl ht
    calc ‖normalizer (1 + (t : ℂ) * I) * riemannZeta (1 + (t : ℂ) * I)‖
        = ‖normalizer (1 + (t : ℂ) * I)‖ * ‖riemannZeta (1 + (t : ℂ) * I)‖ := norm_mul _ _
      _ ≤ (1 / ‖Complex.log ((t : ℂ) - I)‖) * (Real.log t - 0.048) := by
          rw [hN2]
          exact mul_le_mul_of_nonneg_left hD2 (by positivity)
      _ ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul]
          rw [div_le_iff₀ hlogpos']
          linarith

/-- LEAF. Backlund pp. 366 through 368 displays 70, 71 and 73.
The height-fifty half-edge and normalized symmetry control the bottom edge.
No point above the bottom edge occurs here. -/
theorem normalized_bottom_boundary
    (h50 : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
        0.9964 * ((25 : ℝ) / π) ^ ((1 - σ) / 2) * Real.log 50)
    (σ : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖normalizer ((σ : ℂ) + 50 * I) * riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ 1 := by
  sorry

/-- Backlund p. 368, the half-strip maximum argument with explicit damping.
The regularity, three boundary edges and damped top bounds are premises.
This isolates the maximum principle from every zeta and Gamma estimate. -/
theorem half_strip_of_damped_top (f : ℂ → ℂ)
    (hd : DiffContOnCl ℂ f (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioi (50 : ℝ)))
    (hv : ∀ t : ℝ, 50 ≤ t → ‖f (t * I)‖ ≤ 1 ∧ ‖f (1 + t * I)‖ ≤ 1)
    (hb : ∀ σ ∈ Set.Icc (0 : ℝ) 1, ‖f ((σ : ℂ) + 50 * I)‖ ≤ 1)
    (hT : ∀ ε : ℝ, 0 < ε → ∀ H : ℝ, ∃ T : ℝ, max 50 H < T ∧
      ∀ σ ∈ Set.Icc (0 : ℝ) 1,
        ‖Complex.exp ((ε : ℂ) * ((σ : ℂ) + T * I) ^ 2) * f ((σ : ℂ) + T * I)‖ ≤ 1)
    (σ t : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    ‖f ((σ : ℂ) + t * I)‖ ≤ 1 := by
  let z : ℂ := (σ : ℂ) + t * I
  have hεbound (ε : ℝ) (hε : 0 < ε) : ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖ ≤ 1 := by
    obtain ⟨T, hTbig, htop⟩ := hT ε hε t
    have h50T : (50 : ℝ) < T := (le_max_left _ _).trans_lt hTbig
    have htT : t < T := (le_max_right _ _).trans_lt hTbig
    let g : ℂ → ℂ := fun w => Complex.exp ((ε : ℂ) * w ^ 2) * f w
    have hgd : Differentiable ℂ (fun w : ℂ => Complex.exp ((ε : ℂ) * w ^ 2)) := by fun_prop
    have hdg : DiffContOnCl ℂ g (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (50 : ℝ) T) := by
      exact (hgd.diffContOnCl.smul hd).mono (by intro w hw; exact ⟨hw.1, hw.2.1⟩)
    have hsmall (w : ℂ) (hw : w.re ∈ Set.Icc (0 : ℝ) 1) (hwt : 50 ≤ w.im) :
        ‖Complex.exp ((ε : ℂ) * w ^ 2)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      have he : ((ε : ℂ) * w ^ 2).re = ε * (w.re ^ 2 - w.im ^ 2) := by
        simp [pow_two, Complex.mul_re]
      rw [he]
      apply mul_nonpos_of_nonneg_of_nonpos hε.le
      nlinarith [hw.1, hw.2]
    have hboundary : ∀ w ∈ frontier (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (50 : ℝ) T), ‖g w‖ ≤ 1 := by
      intro w hw
      rw [frontier_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
        frontier_Ioo h50T, closure_Ioo h50T.ne, frontier_Ioo (by norm_num : (0 : ℝ) < 1)] at hw
      have hbnd (hwσ : w.re ∈ Set.Icc (0 : ℝ) 1) (hwt : 50 ≤ w.im) (hf : ‖f w‖ ≤ 1) : ‖g w‖ ≤ 1 := by
        dsimp [g]
        rw [norm_mul]
        exact (mul_le_mul (hsmall w hwσ hwt) hf (norm_nonneg _) (by norm_num)).trans (by norm_num)
      rcases hw with hw | hw
      · have hy : w.im = 50 ∨ w.im = T := by
          have hy : w.im ∈ ({50, T} : Set ℝ) := hw.2
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy
        rcases hy with hy | hy
        · apply hbnd hw.1 (by linarith)
          have h := hb w.re hw.1
          have he := Complex.re_add_im w
          norm_num only [hy, Complex.ofReal_ofNat] at he
          rw [he] at h
          exact h
        · have h := htop w.re hw.1
          have he : (w.re : ℂ) + (T : ℂ) * I = w := by
            rw [← hy]
            exact Complex.re_add_im w
          simpa only [he, g] using h
      · have hx : w.re = 0 ∨ w.re = 1 := by
          have hx : w.re ∈ ({0, 1} : Set ℝ) := hw.1
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
        have hwt : w.im ∈ Set.Icc (50 : ℝ) T := hw.2
        rcases hx with hx | hx
        · apply hbnd (by constructor <;> linarith) hwt.1
          have h := (hv w.im hwt.1).1
          have he : (w.im : ℂ) * I = w := by simpa [hx] using Complex.re_add_im w
          simpa only [he] using h
        · apply hbnd (by constructor <;> linarith) hwt.1
          have h := (hv w.im hwt.1).2
          have he : 1 + (w.im : ℂ) * I = w := by simpa [hx] using Complex.re_add_im w
          simpa only [he] using h
    have hz : z ∈ closure (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (50 : ℝ) T) := by
      rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioo h50T.ne]
      change z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (50 : ℝ) T
      simpa [z] using (show σ ∈ Set.Icc (0 : ℝ) 1 ∧ t ∈ Set.Icc (50 : ℝ) T from ⟨hσ, ht, htT.le⟩)
    exact Complex.norm_le_of_forall_mem_frontier_norm_le
      ((isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _)) hdg hboundary hz
  have hc : Continuous (fun ε : ℝ => ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖) := by fun_prop
  have hlim : Tendsto (fun ε : ℝ => ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖f z‖) := by
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hεbound ε hε
  simpa [z] using le_of_tendsto hlim hle

/-- Backlund p. 363 display 57, regularity of the actual normalized function.
The sine stays away from its branch cut in the open half-strip.
Gamma has no poles and the logarithm denominator is nonzero there. -/
theorem normalized_regular :
    DiffContOnCl ℂ (fun s : ℂ => normalizer s * riemannZeta s)
      (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioi (50 : ℝ)) := by
  have hpoint (z : ℂ) (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (hzt : 50 ≤ z.im) :
      DifferentiableAt ℂ (fun s : ℂ => normalizer s * riemannZeta s) z := by
    have hargre : (π * z / 2 : ℂ).re = π * z.re / 2 := by simp [Complex.mul_re]
    have hargim : (π * z / 2 : ℂ).im = π * z.im / 2 := by simp [Complex.mul_im]
    have hsinR (w : ℂ) : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im := by
      rw [Complex.sin_eq]
      simp only [← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
        ← Complex.ofReal_sinh, Complex.add_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, mul_one, add_zero]
    have hsinI (w : ℂ) : (Complex.sin w).im = Real.cos w.re * Real.sinh w.im := by
      rw [Complex.sin_eq]
      simp only [← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
        ← Complex.ofReal_sinh, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, mul_one, add_zero, zero_add]
    have hsinre : (Complex.sin (π * z / 2)).re =
        Real.sin (π * z.re / 2) * Real.cosh (π * z.im / 2) := by rw [hsinR, hargre, hargim]
    have hsinim : (Complex.sin (π * z / 2)).im =
        Real.cos (π * z.re / 2) * Real.sinh (π * z.im / 2) := by rw [hsinI, hargre, hargim]
    have hslit : Complex.sin (π * z / 2) ∈ Complex.slitPlane := by
      change 0 < (Complex.sin (π * z / 2)).re ∨ (Complex.sin (π * z / 2)).im ≠ 0
      by_cases hzpos : 0 < z.re
      · left
        rw [hsinre]
        apply mul_pos _ (Real.cosh_pos _)
        apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
        nlinarith [Real.pi_pos]
      · right
        have hz : z.re = 0 := le_antisymm (le_of_not_gt hzpos) hz0
        rw [hsinim, hz]
        simp only [mul_zero, zero_div, Real.cos_zero, one_mul]
        exact ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
    have harg : DifferentiableAt ℂ (fun s : ℂ => π * s / 2) z := by fun_prop
    have hsinD : DifferentiableAt ℂ (fun s : ℂ => Complex.sin (π * s / 2)) z :=
      Complex.differentiableAt_sin.comp z harg
    have hsqrt := (Complex.differentiableAt_sqrt hslit).comp z hsinD
    have hgamma := (Complex.differentiableAt_Gamma (z / 2) (by
      intro m h
      have hi := congrArg Complex.im h
      simp at hi
      linarith)).comp z ((differentiableAt_id (𝕜 := ℂ) (x := z)).div_const (2 : ℂ))
    have hpow := ((differentiableAt_id (𝕜 := ℂ) (x := z)).neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (show (π : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero))
    have hlogslit : -z * I ∈ Complex.slitPlane := by
      left
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_sub, neg_neg]
      linarith
    have hlog := (Complex.differentiableAt_log hlogslit).comp z
      (differentiableAt_id.neg.mul_const I)
    have hln : Complex.log (-z * I) ≠ 0 := by
      have hlower : (50 : ℝ) ≤ ‖-z * I‖ := by
        have h := Complex.re_le_norm (-z * I)
        simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
          Complex.I_im, mul_zero, mul_one, zero_sub, neg_neg] at h
        exact hzt.trans h
      have hp : 0 < (Complex.log (-z * I)).re := by
        rw [Complex.log_re]
        exact Real.log_pos (by linarith)
      intro h
      rw [h, Complex.zero_re] at hp
      exact lt_irrefl 0 hp
    have hnorm : DifferentiableAt ℂ normalizer z := by
      exact ((hpow.mul hgamma).mul hsqrt).div hlog hln
    have hzeta : z ≠ 1 := by
      intro h
      rw [h] at hzt
      norm_num at hzt
    exact hnorm.mul (differentiableAt_riemannZeta hzeta)
  apply DifferentiableOn.diffContOnCl
  rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioi]
  intro z hz
  exact (hpoint z hz.1.1 hz.1.2 hz.2).differentiableWithinAt

/-- `‖Γ s‖ ≤ Γ(1/2) + Γ(3/2)` for `1/2 ≤ Re s ≤ 3/2`, from the Euler integral. -/
private theorem norm_Gamma_strip_le' {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma (1 / 2) + Real.Gamma (3 / 2) := by
  rw [Complex.Gamma_eq_integral (by linarith), Complex.GammaIntegral]
  have hI1 := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)
  have hI3 := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 3 / 2)
  have hint := hI1.add hI3
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [Real.Gamma_eq_integral (by norm_num), Real.Gamma_eq_integral (by norm_num),
    ← integral_add hI1 hI3]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  have he : 0 < Real.exp (-x) := Real.exp_pos _
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
    Real.norm_of_nonneg he.le, ← mul_add]
  simp only [sub_re, one_re]
  gcongr
  rcases le_or_gt x 1 with hx1 | hx1
  · have hle : x ^ (s.re - 1) ≤ x ^ (1 / 2 - 1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
    have hpos : 0 ≤ x ^ (3 / 2 - 1 : ℝ) := Real.rpow_nonneg hx0.le _
    linarith
  · have hle : x ^ (s.re - 1) ≤ x ^ (3 / 2 - 1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have hpos : 0 ≤ x ^ (1 / 2 - 1 : ℝ) := Real.rpow_nonneg hx0.le _
    linarith

/-- `‖sin (a + b i)‖ ≤ exp b` for `b > 0`. -/
private lemma sin_imag_bound {a b : ℝ} (hb : 0 < b) :
    ‖Complex.sin ((a : ℂ) + (b : ℂ) * I)‖ ≤ Real.exp b := by
  rw [Complex.sin_add_mul_I]
  have hs : ‖Complex.sin ((a : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one a
  have hc : ‖Complex.cos ((a : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one a
  have hcb : ‖Complex.cosh ((b : ℂ))‖ = Real.cosh b := by
    rw [← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos b)]
  have hsb : ‖Complex.sinh ((b : ℂ))‖ = Real.sinh b := by
    rw [← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖Complex.sin (a : ℂ) * Complex.cosh (b : ℂ) +
        Complex.cos (a : ℂ) * Complex.sinh (b : ℂ) * I‖
      ≤ ‖Complex.sin (a : ℂ) * Complex.cosh (b : ℂ)‖ +
        ‖Complex.cos (a : ℂ) * Complex.sinh (b : ℂ) * I‖ := norm_add_le _ _
    _ = ‖Complex.sin (a : ℂ)‖ * Real.cosh b + ‖Complex.cos (a : ℂ)‖ * Real.sinh b := by
        rw [norm_mul, norm_mul, norm_mul, hcb, hsb, Complex.norm_I, mul_one]
    _ ≤ 1 * Real.cosh b + 1 * Real.sinh b := by
        exact add_le_add (mul_le_mul_of_nonneg_right hs (le_of_lt (Real.cosh_pos b)))
          (mul_le_mul_of_nonneg_right hc (le_of_lt (by positivity : 0 < Real.sinh b)))
    _ = Real.exp b := by
        rw [one_mul, one_mul, Real.cosh_add_sinh]

/-- `‖cos (a - b i)‖ ≤ exp b` for `b > 0`. -/
private lemma cos_neg_imag_bound {a b : ℝ} (hb : 0 < b) :
    ‖Complex.cos ((a : ℂ) + ((-b : ℝ) : ℂ) * I)‖ ≤ Real.exp b := by
  rw [Complex.cos_add_mul_I]
  have hs : ‖Complex.sin ((a : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one a
  have hc : ‖Complex.cos ((a : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one a
  have hcb : ‖Complex.cosh (((-b : ℝ)) : ℂ)‖ = Real.cosh b := by
    rw [← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs, Real.cosh_neg,
      abs_of_pos (Real.cosh_pos b)]
  have hsb : ‖Complex.sinh (((-b : ℝ)) : ℂ)‖ = Real.sinh b := by
    rw [← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs, Real.sinh_neg, abs_neg,
      abs_of_pos (by positivity)]
  calc ‖Complex.cos (a : ℂ) * Complex.cosh ((-b : ℝ) : ℂ) -
        Complex.sin (a : ℂ) * Complex.sinh ((-b : ℝ) : ℂ) * I‖
      ≤ ‖Complex.cos (a : ℂ) * Complex.cosh ((-b : ℝ) : ℂ)‖ +
        ‖Complex.sin (a : ℂ) * Complex.sinh ((-b : ℝ) : ℂ) * I‖ := norm_sub_le _ _
    _ = ‖Complex.cos (a : ℂ)‖ * Real.cosh b + ‖Complex.sin (a : ℂ)‖ * Real.sinh b := by
        rw [norm_mul, norm_mul, norm_mul, hcb, hsb, Complex.norm_I, mul_one]
    _ ≤ 1 * Real.cosh b + 1 * Real.sinh b := by
        exact add_le_add (mul_le_mul_of_nonneg_right hc (le_of_lt (Real.cosh_pos b)))
          (mul_le_mul_of_nonneg_right hs (le_of_lt (by positivity : 0 < Real.sinh b)))
    _ = Real.exp b := by
        rw [one_mul, one_mul, Real.cosh_add_sinh]

/-- Growth of `ζ` on the critical strip. -/
private lemma zeta_strip_growth {σ T : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (hT : 50 ≤ T) :
    ‖riemannZeta ((σ : ℂ) + T * I)‖ ≤
      (4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))) * Real.exp (π * T / 2) *
        (1 + T) := by
  have hσ0 : (0 : ℝ) ≤ σ := hσ.1
  have hσ1 : σ ≤ 1 := hσ.2
  have hTpos : 0 < T := by linarith
  have hCgpos : 0 < Real.Gamma (1 / 2) + Real.Gamma (3 / 2) := by
    have h1 := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have h3 := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    linarith
  have hE1 : 1 ≤ Real.exp (π * T / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hnorm : ‖((σ : ℂ) + T * I)‖ ≤ 1 + T := by
    have hsq : ‖((σ : ℂ) + T * I)‖ ^ 2 = σ ^ 2 + T ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have hle : ‖((σ : ℂ) + T * I)‖ ^ 2 ≤ (1 + T) ^ 2 := by
      rw [hsq]
      nlinarith [hσ0, hσ1, hT]
    nlinarith [hle, norm_nonneg ((σ : ℂ) + T * I), hTpos]
  have hbig : 4 * (1 + T) ≤ (4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))) *
      Real.exp (π * T / 2) * (1 + T) := by
    have h1 : (4 : ℝ) ≤ (4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))) *
        Real.exp (π * T / 2) := by
      have h2 : (4 : ℝ) ≤ 4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) := by linarith
      calc (4 : ℝ) ≤ 4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) := h2
        _ = (4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))) * 1 := by ring
        _ ≤ (4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))) * Real.exp (π * T / 2) := by
            exact mul_le_mul_of_nonneg_left hE1 (by linarith)
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  rcases lt_or_ge σ (1 / 2) with hlt | hge
  · -- small real part: functional equation
    set s : ℂ := 1 - ((σ : ℂ) + T * I) with hs
    have hsre : s.re = 1 - σ := by simp [s]
    have hsim : s.im = -T := by simp [s]
    have hsne : ∀ n : ℕ, s ≠ -(n : ℂ) := by
      intro n h
      have hi := congrArg Complex.im h
      simp [s] at hi
      linarith
    have hsne1 : s ≠ 1 := by
      intro h
      have hi := congrArg Complex.im h
      simp [s] at hi
      linarith
    have hFE := riemannZeta_one_sub (s := s) hsne hsne1
    have h1s : 1 - s = (σ : ℂ) + T * I := by simp [s]
    rw [h1s] at hFE
    have hG : ‖Complex.Gamma s‖ ≤ Real.Gamma (1 / 2) + Real.Gamma (3 / 2) :=
      norm_Gamma_strip_le' (by rw [hsre]; linarith) (by rw [hsre]; linarith)
    have hcos : ‖Complex.cos (π * s / 2)‖ ≤ Real.exp (π * T / 2) := by
      have he : π * s / 2 = ((π * (1 - σ) / 2 : ℝ) : ℂ) + ((-(π * T / 2) : ℝ) : ℂ) * I := by
        simp [s]
        push_cast
        ring
      rw [he]
      exact cos_neg_imag_bound (by positivity)
    have hzre : 0 < s.re := by rw [hsre]; linarith
    have hzdist : 1 ≤ ‖s - 1‖ := by
      have him : (s - 1).im = -T := by simp [s]
      have h := Complex.abs_im_le_norm (s - 1)
      rw [him, abs_neg, abs_of_pos hTpos] at h
      linarith
    have hzle := LeanLab.PNTPort.ZetaZeros.norm_zeta_le hzre hzdist
    have hsn : ‖s‖ ≤ 1 + T := by
      have hsq : ‖s‖ ^ 2 = (1 - σ) ^ 2 + T ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [s]
        ring
      have hle : ‖s‖ ^ 2 ≤ (1 + T) ^ 2 := by
        rw [hsq]
        nlinarith [hσ0, hlt, hT]
      nlinarith [hle, norm_nonneg s, hTpos]
    have hz2 : ‖riemannZeta s‖ ≤ 2 + 2 * (1 + T) := by
      have hdiv : ‖s‖ / s.re ≤ 2 * (1 + T) := by
        rw [hsre, div_le_iff₀ (by linarith : (0 : ℝ) < 1 - σ)]
        calc ‖s‖ ≤ 1 + T := hsn
          _ ≤ 2 * (1 + T) * (1 - σ) := by nlinarith [hlt, hT]
      linarith [hdiv, hzle]
    have hpw : ‖(2 * (π : ℂ)) ^ (-s)‖ ≤ 1 := by
      have hb : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
      rw [hb, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have hre : (-s).re = -(1 - σ) := by simp [s]
      rw [hre]
      calc (2 * π : ℝ) ^ (-(1 - σ)) ≤ (2 * π : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
        _ = 1 := by simp
    rw [hFE]
    have hpos2 : 0 < 2 + 2 * (1 + T) := by linarith
    have hposE : 0 < Real.exp (π * T / 2) := Real.exp_pos _
    calc ‖2 * (2 * (π : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (π * s / 2) *
          riemannZeta s‖
        = 2 * ‖(2 * (π : ℂ)) ^ (-s)‖ * ‖Complex.Gamma s‖ * ‖Complex.cos (π * s / 2)‖ *
          ‖riemannZeta s‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul]
          norm_num
      _ ≤ 2 * 1 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) * Real.exp (π * T / 2) *
          (2 + 2 * (1 + T)) := by gcongr
      _ ≤ (4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))) * Real.exp (π * T / 2) *
          (1 + T) := by
          have hG' : (0:ℝ) < Real.Gamma (1 / 2) + Real.Gamma (3 / 2) := hCgpos
          have h1 : 2 * 1 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) * Real.exp (π * T / 2) *
              (2 + 2 * (1 + T))
              ≤ 2 * 1 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) * Real.exp (π * T / 2) *
                (4 * (1 + T)) := by
            have hA : (0:ℝ) ≤ 2 * 1 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) *
                Real.exp (π * T / 2) := by positivity
            exact mul_le_mul_of_nonneg_left (by linarith) hA
          have h2 : 2 * 1 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) * Real.exp (π * T / 2) *
              (4 * (1 + T))
              ≤ (4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))) * Real.exp (π * T / 2) *
                (1 + T) := by
            have hB : (0:ℝ) ≤ Real.exp (π * T / 2) * (1 + T) := by positivity
            have hC : 2 * 1 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) * 4
                ≤ (4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))) := by linarith
            calc 2 * 1 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) * Real.exp (π * T / 2) *
                  (4 * (1 + T))
                = (2 * 1 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) * 4) *
                  (Real.exp (π * T / 2) * (1 + T)) := by ring
              _ ≤ (4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))) *
                  (Real.exp (π * T / 2) * (1 + T)) := mul_le_mul_of_nonneg_right hC hB
              _ = (4 + 8 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))) * Real.exp (π * T / 2) *
                  (1 + T) := by ring
          linarith
  · -- large real part: the ported explicit bound
    have hzre : 0 < ((σ : ℂ) + T * I).re := by
      simp
      linarith [hσ0]
    have hzdist : 1 ≤ ‖((σ : ℂ) + T * I) - 1‖ := by
      have him : (((σ : ℂ) + T * I) - 1).im = T := by simp
      have h := Complex.abs_im_le_norm (((σ : ℂ) + T * I) - 1)
      rw [him, abs_of_pos hTpos] at h
      linarith
    have hzle := LeanLab.PNTPort.ZetaZeros.norm_zeta_le hzre hzdist
    have hdiv : ‖((σ : ℂ) + T * I)‖ / ((σ : ℂ) + T * I).re ≤ 2 * (1 + T) := by
      have hre : ((σ : ℂ) + T * I).re = σ := by simp
      rw [hre, div_le_iff₀ (by linarith : (0 : ℝ) < σ)]
      calc ‖((σ : ℂ) + T * I)‖ ≤ 1 + T := hnorm
        _ ≤ 2 * (1 + T) * σ := by nlinarith [hge, hT]
    linarith [hzle, hdiv, hbig]

/-- The normalised factor at `σ + i T`, for `T ≥ 50`. -/
private lemma normalizer_bound {σ T : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (hT : 50 ≤ T) :
    ‖normalizer ((σ : ℂ) + T * I)‖ ≤
      2 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) * Real.exp (π * T / 2) /
        (T * Real.log T) := by
  have hσ0 : (0 : ℝ) ≤ σ := hσ.1
  have hσ1 : σ ≤ 1 := hσ.2
  have hTpos : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hCgpos : 0 < Real.Gamma (1 / 2) + Real.Gamma (3 / 2) := by
    have h1 := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have h3 := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    linarith
  have hE1 : 1 ≤ Real.exp (π * T / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  set z : ℂ := (σ : ℂ) + T * I with hzdef
  have hzre : z.re = σ := by simp [z]
  have hzim : z.im = T := by simp [z]
  have hznorm : T ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rw [hzim, abs_of_pos hTpos] at h
    exact h
  have hpi : ‖(π : ℂ) ^ (-z / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-z / 2).re = -σ / 2 := by simp [z]
    rw [hre]
    calc π ^ (-σ / 2) ≤ π ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = 1 := by simp
  have hGamma : ‖Complex.Gamma (z / 2)‖ ≤
      2 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) / T := by
    have hwne : z / 2 ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      simp [z] at hi
      linarith
    have hadd := Complex.Gamma_add_one (z / 2) hwne
    have heq : ‖Complex.Gamma (z / 2)‖ = ‖Complex.Gamma (1 + z / 2)‖ / ‖z / 2‖ := by
      rw [show (1 : ℂ) + z / 2 = z / 2 + 1 by ring, hadd, norm_mul]
      have hwn : ‖z / 2‖ ≠ 0 := (norm_pos_iff.mpr hwne).ne'
      field_simp
    have hz2 : (1 + z / 2).re = 1 + σ / 2 := by simp [z]
    have hstrip := norm_Gamma_strip_le' (s := 1 + z / 2)
      (by rw [hz2]; linarith) (by rw [hz2]; linarith)
    have hzn : ‖z / 2‖ = ‖z‖ / 2 := by rw [norm_div]; norm_num
    have hhalf : T / 2 ≤ ‖z / 2‖ := by rw [hzn]; linarith
    have hz2n : (0:ℝ) < ‖z / 2‖ := norm_pos_iff.mpr hwne
    rw [heq, div_le_div_iff₀ hz2n hTpos]
    nlinarith [hstrip, hhalf, hCgpos, norm_nonneg (Complex.Gamma (1 + z / 2))]
  have hsqrt : ‖Complex.sqrt (Complex.sin (π * z / 2))‖ ≤ Real.exp (π * T / 2) := by
    rw [cnorm_sqrt]
    have hsin : ‖Complex.sin (π * z / 2)‖ ≤ Real.exp (π * T / 2) := by
      have he : π * z / 2 = ((π * σ / 2 : ℝ) : ℂ) + ((π * T / 2 : ℝ) : ℂ) * I := by
        simp [z]; push_cast; ring
      rw [he]
      exact sin_imag_bound (by positivity)
    calc Real.sqrt ‖Complex.sin (π * z / 2)‖ ≤ Real.sqrt (Real.exp (π * T / 2)) :=
          Real.sqrt_le_sqrt hsin
      _ ≤ Real.exp (π * T / 2) := by
          have h1 : Real.sqrt (Real.exp (π * T / 2)) ≤
              Real.sqrt (Real.exp (π * T / 2) ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith [hE1, Real.exp_pos (π * T / 2)]
          calc Real.sqrt (Real.exp (π * T / 2))
              ≤ Real.sqrt (Real.exp (π * T / 2) ^ 2) := h1
            _ = Real.exp (π * T / 2) := Real.sqrt_sq (by positivity)
  have hlog : Real.log T ≤ ‖Complex.log (-z * I)‖ := by
    have hre : (Complex.log (-z * I)).re = Real.log ‖-z * I‖ := Complex.log_re _
    have harg : -z * I = (T : ℂ) - (σ : ℂ) * I := by
      have h1 : ((T : ℂ) * I) * I = -(T : ℂ) := by
        rw [mul_assoc, Complex.I_mul_I]; ring
      simp only [z]
      rw [show -((σ : ℂ) + (T : ℂ) * I) * I =
        -((σ : ℂ) * I) - ((T : ℂ) * I) * I by ring, h1]
      ring
    have hge : T ≤ ‖-z * I‖ := by
      rw [harg]
      have h := Complex.re_le_norm ((T : ℂ) - (σ : ℂ) * I)
      simpa using h
    have hlogmono : Real.log T ≤ Real.log ‖-z * I‖ := Real.log_le_log hTpos hge
    linarith [hre, hlogmono, Complex.re_le_norm (Complex.log (-z * I))]
  have hnumeq : ‖normalizer z‖ = ‖(π : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma (z / 2)‖ *
      ‖Complex.sqrt (Complex.sin (π * z / 2))‖ / ‖Complex.log (-z * I)‖ := by
    rw [normalizer, norm_div, norm_mul, norm_mul]
  rw [hnumeq]
  have hlogpos' : 0 < ‖Complex.log (-z * I)‖ := lt_of_lt_of_le hlogT hlog
  have hnum : ‖(π : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma (z / 2)‖ *
      ‖Complex.sqrt (Complex.sin (π * z / 2))‖ ≤
      1 * (2 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) / T) * Real.exp (π * T / 2) := by
    have hnn2 : (0 : ℝ) ≤ 2 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) / T :=
      div_nonneg (by linarith) (le_of_lt hTpos)
    have hnn3 : (0 : ℝ) ≤ Real.exp (π * T / 2) := (Real.exp_pos _).le
    have hb2 : (0 : ℝ) ≤ 1 * (2 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) / T) := by
      have := hnn2; linarith
    exact mul_le_mul (mul_le_mul hpi hGamma (norm_nonneg _) (by norm_num)) hsqrt
      (norm_nonneg _) hb2
  have hinv : (‖Complex.log (-z * I)‖)⁻¹ ≤ (Real.log T)⁻¹ := by
    rw [inv_le_inv₀ hlogpos' hlogT]
    exact hlog
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hstep1 : ‖(π : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma (z / 2)‖ *
        ‖Complex.sqrt (Complex.sin (π * z / 2))‖ * (‖Complex.log (-z * I)‖)⁻¹
      ≤ (1 * (2 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) / T) *
        Real.exp (π * T / 2)) * (Real.log T)⁻¹ := by
    have hbA : (0:ℝ) ≤ 1 * (2 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) / T) *
        Real.exp (π * T / 2) := by
      have h1 : (0:ℝ) ≤ 2 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) / T :=
        div_nonneg (by linarith) (le_of_lt hTpos)
      exact mul_nonneg (mul_nonneg (by norm_num) h1) (Real.exp_pos _).le
    exact mul_le_mul hnum hinv (by positivity) hbA
  have hstep2 : (1 * (2 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) / T) *
      Real.exp (π * T / 2)) * (Real.log T)⁻¹ =
      2 * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) * Real.exp (π * T / 2) /
        (T * Real.log T) := by
    field_simp
  calc ‖(π : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma (z / 2)‖ *
        ‖Complex.sqrt (Complex.sin (π * z / 2))‖ * (‖Complex.log (-z * I)‖)⁻¹
      ≤ _ := hstep1
    _ = _ := hstep2

/-- The Gaussian damping factor. -/
private lemma exp_damping (ε : ℝ) (hε : 0 ≤ ε) {σ T : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖Complex.exp ((ε : ℂ) * ((σ : ℂ) + T * I) ^ 2)‖ ≤ Real.exp (ε * (1 - T ^ 2)) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : ((ε : ℂ) * ((σ : ℂ) + T * I) ^ 2).re = ε * (σ ^ 2 - T ^ 2) := by
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hre]
  have hσ0 : 0 ≤ σ := hσ.1
  have hσ1 : σ ≤ 1 := hσ.2
  have hsq : σ ^ 2 ≤ 1 := by nlinarith
  nlinarith [hsq, hε]

/-- Elementary real-arithmetic step for the damped top edge. -/
private lemma final_bound (ε T G : ℝ) (hG : 0 ≤ G) (hT : 50 ≤ T) :
    Real.exp (ε * (1 - T ^ 2)) *
        ((2 * G * Real.exp (π * T / 2) / (T * Real.log T)) *
          ((4 + 8 * G) * Real.exp (π * T / 2) * (1 + T)))
      ≤ 16 * G * (4 + 8 * G) * Real.exp ε * Real.exp (-(ε * T ^ 2) + π * T) := by
  have hTpos : 0 < T := by linarith
  have hlog1 : 1 ≤ Real.log T := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log T :=
      Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
    rwa [Real.log_exp] at h1
  have hlogpos : 0 < Real.log T := by linarith
  have hTlog : 0 < T * Real.log T := mul_pos hTpos hlogpos
  have hratio : (1 + T) / (T * Real.log T) ≤ 2 := by
    have h1 : (1 + T) / T ≤ 2 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < T)]
      linarith
    have h2 : (0 : ℝ) ≤ (1 + T) / T := div_nonneg (by linarith) (by linarith)
    have h3 : (1 + T) / (T * Real.log T) = ((1 + T) / T) / Real.log T := by
      rw [div_div]
    rw [h3, div_le_iff₀ hlogpos]
    nlinarith [h1, hlog1, h2]
  have hE2 : Real.exp (π * T / 2) * Real.exp (π * T / 2) = Real.exp (π * T) := by
    rw [← Real.exp_add]; ring_nf
  have hD : Real.exp (ε * (1 - T ^ 2)) = Real.exp ε * Real.exp (-(ε * T ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have key : Real.exp (ε * (1 - T ^ 2)) *
        ((2 * G * Real.exp (π * T / 2) / (T * Real.log T)) *
          ((4 + 8 * G) * Real.exp (π * T / 2) * (1 + T)))
      = 2 * G * (4 + 8 * G) * Real.exp (ε * (1 - T ^ 2)) *
          (Real.exp (π * T / 2) * Real.exp (π * T / 2)) *
            ((1 + T) / (T * Real.log T)) := by
    field_simp
  have hstepA : 2 * G * (4 + 8 * G) * Real.exp (ε * (1 - T ^ 2)) *
        (Real.exp (π * T / 2) * Real.exp (π * T / 2)) * ((1 + T) / (T * Real.log T))
      ≤ 2 * G * (4 + 8 * G) * Real.exp (ε * (1 - T ^ 2)) *
        (Real.exp (π * T / 2) * Real.exp (π * T / 2)) * 2 := by
    apply mul_le_mul_of_nonneg_left hratio
    have h1 : (0:ℝ) ≤ 2 * G := by linarith
    have h2 : (0:ℝ) ≤ 4 + 8 * G := by linarith
    have h3 : (0:ℝ) ≤ Real.exp (ε * (1 - T ^ 2)) := (Real.exp_pos _).le
    have h4 : (0:ℝ) ≤ Real.exp (π * T / 2) * Real.exp (π * T / 2) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  have hstepB : 2 * G * (4 + 8 * G) * Real.exp (ε * (1 - T ^ 2)) *
        (Real.exp (π * T / 2) * Real.exp (π * T / 2)) * 2
      = 4 * G * (4 + 8 * G) * Real.exp ε * Real.exp (-(ε * T ^ 2) + π * T) := by
    rw [hE2, hD]
    have hcomb : Real.exp (-(ε * T ^ 2)) * Real.exp (π * T)
        = Real.exp (-(ε * T ^ 2) + π * T) := by
      rw [← Real.exp_add]
    calc 2 * G * (4 + 8 * G) * (Real.exp ε * Real.exp (-(ε * T ^ 2))) *
          Real.exp (π * T) * 2
        = 4 * G * (4 + 8 * G) * Real.exp ε *
            (Real.exp (-(ε * T ^ 2)) * Real.exp (π * T)) := by ring
      _ = 4 * G * (4 + 8 * G) * Real.exp ε * Real.exp (-(ε * T ^ 2) + π * T) := by
          rw [hcomb]
  have hstepC : 4 * G * (4 + 8 * G) * Real.exp ε * Real.exp (-(ε * T ^ 2) + π * T)
      ≤ 16 * G * (4 + 8 * G) * Real.exp ε * Real.exp (-(ε * T ^ 2) + π * T) := by
    have h1 : (0:ℝ) ≤ G := hG
    have h2 : (0:ℝ) ≤ 4 + 8 * G := by linarith
    have h3 : (0:ℝ) ≤ Real.exp ε := (Real.exp_pos _).le
    have h4 : (0:ℝ) ≤ Real.exp (-(ε * T ^ 2) + π * T) := (Real.exp_pos _).le
    have h5 : (0:ℝ) ≤ G * (4 + 8 * G) * Real.exp ε * Real.exp (-(ε * T ^ 2) + π * T) :=
      mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
    nlinarith [h5]
  rw [key]
  calc 2 * G * (4 + 8 * G) * Real.exp (ε * (1 - T ^ 2)) *
        (Real.exp (π * T / 2) * Real.exp (π * T / 2)) * ((1 + T) / (T * Real.log T))
      ≤ 2 * G * (4 + 8 * G) * Real.exp (ε * (1 - T ^ 2)) *
        (Real.exp (π * T / 2) * Real.exp (π * T / 2)) * 2 := hstepA
    _ = 4 * G * (4 + 8 * G) * Real.exp ε * Real.exp (-(ε * T ^ 2) + π * T) := hstepB
    _ ≤ 16 * G * (4 + 8 * G) * Real.exp ε * Real.exp (-(ε * T ^ 2) + π * T) := hstepC

/-- LEAF. Backlund p. 368, polynomial growth from displays 13 and 67.
Gaussian damping gives an arbitrarily high horizontal top with norm at most one.
No boundary estimate or maximum principle is assumed. -/
theorem normalized_damped_top (ε : ℝ) (hε : 0 < ε) (H : ℝ) :
    ∃ T : ℝ, max 50 H < T ∧ ∀ σ ∈ Set.Icc (0 : ℝ) 1,
      ‖Complex.exp ((ε : ℂ) * ((σ : ℂ) + T * I) ^ 2) *
        (normalizer ((σ : ℂ) + T * I) * riemannZeta ((σ : ℂ) + T * I))‖ ≤ 1 := by

  set G : ℝ := Real.Gamma (1 / 2) + Real.Gamma (3 / 2) with hG
  have hGpos : 0 < G := by
    rw [hG]
    have h1 := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have h3 := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    linarith
  have hG1 : 1 ≤ G := by
    rw [hG]
    have h1 : (1 : ℝ) ≤ Real.Gamma (1 / 2) := by
      rw [Real.Gamma_one_half_eq]
      exact Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three])
    have h3 : 0 < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    linarith
  have hK1 : 1 ≤ 16 * G * (4 + 8 * G) * Real.exp ε := by
    have h4 : (1 : ℝ) ≤ Real.exp ε := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hε.le
    have h5 : (1 : ℝ) ≤ 4 + 8 * G := by linarith
    have hp1 : (0:ℝ) < 16 * G := by nlinarith [hG1]
    have hp2 : (0:ℝ) < 4 + 8 * G := by linarith
    have hp0 : (0:ℝ) < 16 * G * (4 + 8 * G) := by nlinarith [hp1, hp2]
    calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ 16 * G * (4 + 8 * G) * Real.exp ε :=
          mul_le_mul (mul_le_mul (mul_le_mul (by norm_num : (1:ℝ) ≤ 16) hG1
            (by norm_num) (by norm_num)) h5 (by norm_num) hp1.le) h4 (by norm_num) hp0.le
  set L : ℝ := Real.log (16 * G * (4 + 8 * G) * Real.exp ε) with hL
  set r : ℝ := Real.sqrt (2 * L / ε) with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  set T : ℝ := max (max 50 H) 1 + (6 * π / ε + r + 1) with hT
  have h6pi : (0:ℝ) < 6 * π / ε := div_pos (by positivity) hε
  have hTge : max (max 50 H) 1 ≤ T := by
    rw [hT]; linarith [h6pi, hr0]
  have hTgt : max (max 50 H) 1 < T := by
    rw [hT]; linarith [h6pi, hr0]
  have hT50 : 50 ≤ T := le_trans (le_trans (le_max_left 50 H) (le_max_left _ 1)) hTge
  have hTpos : 0 < T := by linarith
  have hmax1 : (1:ℝ) ≤ max (max 50 H) 1 := le_max_right _ _
  have hT6 : 6 * π / ε ≤ T := by
    have h1 : 6 * π / ε ≤ max (max 50 H) 1 + (6 * π / ε + r + 1) := by
      linarith [hr0, hmax1]
    rwa [← hT] at h1
  have hTr : r ≤ T := by
    have h1 : r ≤ max (max 50 H) 1 + (6 * π / ε + r + 1) := by
      linarith [h6pi, hmax1]
    rwa [← hT] at h1
  refine ⟨T, lt_of_le_of_lt (le_max_left (max 50 H) 1) hTgt, ?_⟩
  intro σ hσ
  have hstep : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖Complex.exp ((ε : ℂ) * ((τ : ℂ) + T * I) ^ 2) *
        (normalizer ((τ : ℂ) + T * I) * riemannZeta ((τ : ℂ) + T * I))‖ ≤
        (16 * G * (4 + 8 * G) * Real.exp ε) * Real.exp (-(ε * T ^ 2) + π * T) := by
    intro τ hτ
    have hτ0 : (0:ℝ) ≤ τ := hτ.1
    have hexp := exp_damping (T := T) ε hε.le hτ
    have hN := normalizer_bound hτ hT50
    rw [← hG] at hN
    have hZ := zeta_strip_growth hτ hT50
    rw [← hG] at hZ
    have hTlogpos : 0 < Real.log T := Real.log_pos (by linarith)
    have hdN : (0 : ℝ) ≤ 2 * G * Real.exp (π * T / 2) / (T * Real.log T) :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hGpos.le) (Real.exp_pos _).le)
        (le_of_lt (mul_pos hTpos hTlogpos))
    have hdZ : (0 : ℝ) ≤ (4 + 8 * G) * Real.exp (π * T / 2) * (1 + T) :=
      mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) (by linarith)
    have hNζ : ‖normalizer ((τ : ℂ) + T * I)‖ * ‖riemannZeta ((τ : ℂ) + T * I)‖ ≤
        (2 * G * Real.exp (π * T / 2) / (T * Real.log T)) *
          ((4 + 8 * G) * Real.exp (π * T / 2) * (1 + T)) :=
      mul_le_mul hN hZ (norm_nonneg _) hdN
    calc ‖Complex.exp ((ε : ℂ) * ((τ : ℂ) + T * I) ^ 2) *
          (normalizer ((τ : ℂ) + T * I) * riemannZeta ((τ : ℂ) + T * I))‖
        = ‖Complex.exp ((ε : ℂ) * ((τ : ℂ) + T * I) ^ 2)‖ *
          (‖normalizer ((τ : ℂ) + T * I)‖ * ‖riemannZeta ((τ : ℂ) + T * I)‖) := by
          rw [norm_mul, norm_mul]
      _ ≤ Real.exp (ε * (1 - T ^ 2)) * ((2 * G * Real.exp (π * T / 2) / (T * Real.log T)) *
          ((4 + 8 * G) * Real.exp (π * T / 2) * (1 + T))) :=
          mul_le_mul hexp hNζ (by positivity) (Real.exp_pos _).le
      _ ≤ (16 * G * (4 + 8 * G) * Real.exp ε) * Real.exp (-(ε * T ^ 2) + π * T) :=
          final_bound ε T G hGpos.le hT50
  refine (hstep σ hσ).trans ?_
  have hs : 2 * L / ε ≤ T ^ 2 := by
    have h0' : 0 ≤ L := by rw [hL]; exact Real.log_nonneg hK1
    have h0 : 0 ≤ 2 * L / ε := div_nonneg (by linarith) hε.le
    have hsq : r ^ 2 = 2 * L / ε := by rw [hr]; exact Real.sq_sqrt h0
    nlinarith [hTr, hsq, hr0, hTpos]
  have hlogK : L ≤ ε * T ^ 2 / 2 := by
    have h2 : 2 * L ≤ T ^ 2 * ε := by
      rw [div_le_iff₀ hε] at hs
      linarith [hs]
    nlinarith [h2]
  have hKpos : (0:ℝ) < 16 * G * (4 + 8 * G) * Real.exp ε := by
    have h1 : (0:ℝ) < 16 * G := by nlinarith [hGpos]
    have h2 : (0:ℝ) < 4 + 8 * G := by linarith
    exact mul_pos (mul_pos h1 h2) (Real.exp_pos ε)
  have hKle : 16 * G * (4 + 8 * G) * Real.exp ε ≤ Real.exp (ε * T ^ 2 / 2) := by
    rw [hL] at hlogK
    rw [← Real.exp_log hKpos]
    exact Real.exp_le_exp.mpr hlogK
  have hT6' : π * T ≤ ε * T ^ 2 / 2 := by
    have h1 : 6 * π ≤ ε * T := by
      rw [div_le_iff₀ hε] at hT6
      linarith [hT6]
    nlinarith [h1, hTpos]
  calc (16 * G * (4 + 8 * G) * Real.exp ε) * Real.exp (-(ε * T ^ 2) + π * T)
      ≤ Real.exp (ε * T ^ 2 / 2) * Real.exp (-(ε * T ^ 2 / 2)) := by
        apply mul_le_mul hKle _ (Real.exp_pos _).le (by positivity)
        exact Real.exp_le_exp.mpr (by linarith)
    _ = 1 := by
        rw [← Real.exp_add, show ε * T ^ 2 / 2 + -(ε * T ^ 2 / 2) = 0 by ring, Real.exp_zero]

/-- Backlund p. 368, the Phragmen Lindelof step after display 73.
CONDITIONAL ON normalized_damped_top. Regularity is proved.
The actual normalized function has polynomial growth by display 13 and 67.
Boundary bounds are explicit premises. Gamma and sine boundary estimates
are absent from this leaf. -/
theorem normalized_half_strip
    (hv : ∀ t : ℝ, 50 ≤ t →
      ‖normalizer (t * I) * riemannZeta (t * I)‖ ≤ 1 ∧
      ‖normalizer (1 + t * I) * riemannZeta (1 + t * I)‖ ≤ 1)
    (hb : ∀ σ ∈ Set.Icc (0 : ℝ) 1,
      ‖normalizer ((σ : ℂ) + 50 * I) * riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ 1)
    (σ t : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    ‖normalizer ((σ : ℂ) + t * I) * riemannZeta ((σ : ℂ) + t * I)‖ ≤ 1 := by
  exact half_strip_of_damped_top (fun s : ℂ => normalizer s * riemannZeta s)
    normalized_regular hv hb normalized_damped_top σ t hσ ht

/-- LEAF. Backlund p. 365 displays 60 through 68, lower normalization bound.
This involves only Gamma, sine, logarithm and powers, with no zeta value.
The factor one minus four over t squared is inverted algebraically. -/
theorem normalizer_lower (σ t : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    1 ≤ ‖normalizer ((σ : ℂ) + t * I)‖ *
      (t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t) := by
  sorry

/-- Backlund p. 363 display 56, the exact original strip implication.
CONDITIONAL ON the remaining strictly smaller normalized analytic leaves. -/
theorem strip56_of_boundary
    (h54 : ∀ σ t : ℝ, 1 ≤ σ → 50 ≤ t →
      ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ Real.log t - 0.048)
    (h50 : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
        0.9964 * ((25 : ℝ) / π) ^ ((1 - σ) / 2) * Real.log 50)
    (σ t : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t := by
  have hp := normalized_half_strip (normalized_vertical_boundary h54)
    (normalized_bottom_boundary h50) σ t hσ ht
  rw [norm_mul] at hp
  have hw := normalizer_lower σ t hσ ht
  have hd : 0 < t ^ 2 - 4 := by nlinarith
  have hm : 0 ≤ t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t := by
    exact mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) hd.le)
      (Real.rpow_nonneg (by positivity) _)) (Real.log_nonneg (by linarith))
  calc
    _ = 1 * ‖riemannZeta ((σ : ℂ) + t * I)‖ := by ring
    _ ≤ (‖normalizer ((σ : ℂ) + t * I)‖ *
        (t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t)) *
        ‖riemannZeta ((σ : ℂ) + t * I)‖ :=
      mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = (t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t) *
        (‖normalizer ((σ : ℂ) + t * I)‖ * ‖riemannZeta ((σ : ℂ) + t * I)‖) := by ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hp hm

end LeanLab.RamareSaouter2003.Decomp563c

#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalizer
#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalized_vertical_boundary
#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalized_bottom_boundary
#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalized_half_strip
#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalizer_lower
#print axioms LeanLab.RamareSaouter2003.Decomp563c.strip56_of_boundary

#print axioms LeanLab.RamareSaouter2003.Decomp563c.half_strip_of_damped_top

#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalized_regular

#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalized_damped_top
