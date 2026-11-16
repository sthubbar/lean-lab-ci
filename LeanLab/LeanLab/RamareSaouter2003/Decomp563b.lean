import Mathlib
import LeanLab.RamareSaouter2003.Stirling518

/-!
Backlund pp. 368 and 369 displays 74 through 76.
The zeta functional equation is supplied by Mathlib.
The remaining leaf concerns only the Gamma norm from the shifted Stirling remainder.
AI wrote the Lean code. Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp563b
open Real Complex

section GammaGrowthAux

open MeasureTheory Filter
open scoped Topology

/-! ## Auxiliary lemmas for display 74 -/

private lemma norm_shift_pos (s : ℂ) (hs : 0 < s.re) {x : ℝ} (hx : 0 ≤ x) : 0 < ‖s + x‖ := by
  have h : 0 < (s + x).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  exact norm_pos_iff.mpr (fun hzero => by rw [hzero] at h; exact lt_irrefl 0 h)

/-- `arctan x ≤ x - x³/3 + x⁵` for `x ≥ 0`. -/
private lemma arctan_le_taylor {x : ℝ} (hx : 0 ≤ x) :
    Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 := by
  have hcont : Continuous fun t : ℝ => 1 / (1 + t ^ 2) :=
    continuous_const.div (by fun_prop) (fun t => by positivity)
  have hint : (∫ t : ℝ in (0 : ℝ)..x, 1 / (1 + t ^ 2)) = Real.arctan x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.arctan)
      (f' := fun t : ℝ => 1 / (1 + t ^ 2)) (fun t _ => Real.hasDerivAt_arctan t)
      (hcont.intervalIntegrable 0 x)]
    simp
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) x, 1 / (1 + t ^ 2) ≤ 1 - t ^ 2 + t ^ 4 := by
    intro t ht
    have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [div_le_iff₀ h1]
    nlinarith [pow_nonneg ht.1 6]
  have hg : IntervalIntegrable (fun t : ℝ => 1 - t ^ 2 + t ^ 4) volume (0 : ℝ) x :=
    (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2 + t ^ 4).intervalIntegrable 0 x
  have hmono := intervalIntegral.integral_mono_on hx (hcont.intervalIntegrable 0 x) hg hle
  have hval : (∫ t : ℝ in (0 : ℝ)..x, (1 - t ^ 2 + t ^ 4)) = x - x ^ 3 / 3 + x ^ 5 / 5 := by
    simp
    try ring
  rw [hval, hint] at hmono
  have h5 : x ^ 5 / 5 ≤ x ^ 5 := by nlinarith [pow_nonneg hx 5]
  linarith

private lemma log_le_self_add {u : ℝ} (hu : 0 ≤ u) : Real.log (1 + u) ≤ u := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + u by linarith)
  linarith

private lemma neg_log_le {u : ℝ} (hu : 0 ≤ u) : -(Real.log (1 + u)) ≤ -(u - u ^ 2) := by
  have h1 : (0:ℝ) < 1 + u := by linarith
  have h := Real.one_sub_inv_le_log_of_pos h1
  have h2 : 1 - (1 + u)⁻¹ = u / (1 + u) := by
    field_simp
    ring
  rw [h2] at h
  have h3 : u - u ^ 2 ≤ u / (1 + u) := by
    rw [le_div_iff₀ h1]
    nlinarith [pow_nonneg hu 3]
  linarith

/-- The norm of the Euler limit sequence, in logarithmic form. -/
private lemma log_norm_GammaSeq (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    Real.log ‖Complex.GammaSeq s (n + 1)‖ =
      s.re * Real.log ((n : ℝ) + 1) + Real.log (((n + 1).factorial : ℕ) : ℝ) -
        ∑ k ∈ Finset.range (n + 2), Real.log ‖s + (k : ℂ)‖ := by
  have hn : (0 : ℕ) < n + 1 := Nat.succ_pos n
  have hden : (0 : ℝ) < ∏ j ∈ Finset.range (n + 2), ‖s + (j : ℂ)‖ :=
    Finset.prod_pos (fun j _ => norm_shift_pos s hs (Nat.cast_nonneg j))
  have hmul : ‖Complex.GammaSeq s (n + 1)‖ =
      ((n : ℝ) + 1) ^ s.re * (((n + 1).factorial : ℕ) : ℝ) /
        ∏ j ∈ Finset.range (n + 2), ‖s + (j : ℂ)‖ := by
    rw [Complex.GammaSeq, norm_div, norm_mul, norm_prod, Complex.norm_natCast_cpow_of_pos hn,
      Complex.norm_natCast]
    push_cast
    ring
  rw [hmul, Real.log_div (by positivity) (ne_of_gt hden),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
    Real.log_prod (s := Finset.range (n + 2)) (f := fun j : ℕ => ‖s + (j : ℂ)‖)
      (fun j _ => (norm_shift_pos s hs (Nat.cast_nonneg j)).ne')]
  try ring

set_option maxHeartbeats 4000000 in
/-- The Euler–Maclaurin expansion of `log Γ` in the upper half plane. -/
private lemma log_norm_Gamma_stirling {s : ℂ} (hre : 0 < s.re) (him : 0 < s.im) :
    Real.log ‖Complex.Gamma s‖ =
      (s.re - 1 / 2) * Real.log ‖s‖ - s.im * s.arg - s.re + (1 / 2) * Real.log (2 * π) +
        (1 / (12 * s)).re - (1 / (360 * s ^ 3)).re -
        (1 / 4) * (∫ x : ℝ in Set.Ioi 0,
          (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re := by
  set f1 : ℕ → ℝ := fun n =>
    -(((s + ((n + 1 : ℕ) : ℂ) + 1 / 2) *
      (Complex.log (s + ((n + 1 : ℕ) : ℂ)) - ((Real.log (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ))).re)
    with hf1
  set f2 : ℕ → ℝ := fun n =>
    Real.log (((n + 1).factorial : ℕ) : ℝ) -
      ((((n + 1 : ℕ) : ℝ)) + 1 / 2) * Real.log (((n + 1 : ℕ) : ℝ)) + (((n + 1 : ℕ) : ℝ))
    with hf2
  set f5 : ℕ → ℝ := fun n =>
    -(((1 / (s + ((n + 1 : ℕ) : ℂ)) - 1 / s) / 12).re) +
      ((((1 / (s + ((n + 1 : ℕ) : ℂ)) ^ 3 - 1 / s ^ 3)) / 360).re) with hf5
  set f6 : ℕ → ℝ := fun n =>
    -((∫ x : ℝ in (0 : ℝ)..(((n + 1 : ℕ)) : ℝ),
      (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)) / 4).re with hf6
  set K : ℝ := s.re + ((s - 1 / 2) * Complex.log s - s).re with hK
  have hnorm : Tendsto (fun n : ℕ => Real.log ‖Complex.GammaSeq s (n + 1)‖) atTop
      (𝓝 (Real.log ‖Complex.Gamma s‖)) := by
    have h0 : Tendsto (fun n : ℕ => Complex.GammaSeq s (n + 1)) atTop (𝓝 (Complex.Gamma s)) :=
      (Complex.GammaSeq_tendsto_Gamma s).comp (tendsto_add_atTop_nat 1)
    have hn := h0.norm
    have hpos : ‖Complex.Gamma s‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact Complex.Gamma_ne_zero_of_re_pos hre
    exact (Real.continuousAt_log hpos).tendsto.comp hn
  have hA : Tendsto (fun n : ℕ => ((s + ((n + 1 : ℕ) : ℂ) + 1 / 2) *
      (Complex.log (s + ((n + 1 : ℕ) : ℂ)) - ((Real.log (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ))).re)
      atTop (𝓝 s.re) := by
    have h0 := (LeanLab.RamareSaouter2003.Stirling518.logarithmic_endpoint_limit s him).comp
      (tendsto_add_atTop_nat 1)
    have h1 : Tendsto (fun n : ℕ => (s + ((n + 1 : ℕ) : ℂ) + 1 / 2) *
        (Complex.log (s + ((n + 1 : ℕ) : ℂ)) - ((Real.log (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ)) - s)
        atTop (𝓝 (0 : ℂ)) := h0
    have h2 : Tendsto (fun n : ℕ => ((s + ((n + 1 : ℕ) : ℂ) + 1 / 2) *
        (Complex.log (s + ((n + 1 : ℕ) : ℂ)) - ((Real.log (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ)) - s).re)
        atTop (𝓝 (0 : ℝ)) := (Complex.continuous_re.tendsto (0 : ℂ)).comp h1
    have h3 : Tendsto (fun n : ℕ => ((s + ((n + 1 : ℕ) : ℂ) + 1 / 2) *
        (Complex.log (s + ((n + 1 : ℕ) : ℂ)) - ((Real.log (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ))).re - s.re)
        atTop (𝓝 (0 : ℝ)) := by
      refine Tendsto.congr' (Eventually.of_forall (fun n => ?_)) h2
      exact (Complex.sub_re _ _).symm
    have h4 := h3.add_const s.re
    rw [zero_add] at h4
    refine Tendsto.congr' (Eventually.of_forall (fun n => ?_)) h4
    simp
  have hB : Tendsto f2 atTop (𝓝 (Real.log (Real.sqrt (2 * π)))) := by
    have h := (LeanLab.RamareSaouter2003.Stirling518.log_factorial_limit).comp
      (tendsto_add_atTop_nat 1)
    rw [hf2]
    refine Tendsto.congr' (Eventually.of_forall (fun n => ?_)) h
    simp only [Function.comp_apply]
    ring
  have hE : Tendsto f5 atTop (𝓝 ((1 / (12 * s)).re - (1 / (360 * s ^ 3)).re)) := by
    have hs0 : s ≠ 0 := by intro h; rw [h] at him; simp at him
    have hi : Tendsto (fun n : ℕ => (s + ((n + 1 : ℕ) : ℂ))⁻¹) atTop (𝓝 0) :=
      (LeanLab.RamareSaouter2003.Stirling518.inv_shift_limit s him).comp
        (tendsto_add_atTop_nat 1)
    have hi' : Tendsto (fun n : ℕ => (1 / (s + ((n + 1 : ℕ) : ℂ)))) atTop (𝓝 0) := by
      refine Tendsto.congr' (Eventually.of_forall (fun n => ?_)) hi
      simp [one_div]
    have hcube : Tendsto (fun n : ℕ => 1 / (s + ((n + 1 : ℕ) : ℂ)) ^ 3) atTop (𝓝 0) := by
      have h := hi'.pow 3
      rw [show (0 : ℂ) ^ 3 = 0 by norm_num] at h
      refine Tendsto.congr' (Eventually.of_forall (fun n => ?_)) h
      simp only [one_div_pow]
    have h12 : Tendsto (fun n : ℕ => ((1 / (s + ((n + 1 : ℕ) : ℂ)) - 1 / s) / 12))
        atTop (𝓝 ((0 - 1 / s) / 12)) := (hi'.sub tendsto_const_nhds).div_const 12
    have h360 : Tendsto (fun n : ℕ => ((1 / (s + ((n + 1 : ℕ) : ℂ)) ^ 3 - 1 / s ^ 3)) / 360)
        atTop (𝓝 ((0 - 1 / s ^ 3) / 360)) := (hcube.sub tendsto_const_nhds).div_const 360
    have h12r : Tendsto (fun n : ℕ => (((1 / (s + ((n + 1 : ℕ) : ℂ)) - 1 / s) / 12)).re)
        atTop (𝓝 (((0 - 1 / s) / 12).re)) := (Complex.continuous_re.tendsto _).comp h12
    have h360r : Tendsto (fun n : ℕ => ((((1 / (s + ((n + 1 : ℕ) : ℂ)) ^ 3 - 1 / s ^ 3)) / 360).re))
        atTop (𝓝 ((((0 - 1 / s ^ 3)) / 360).re)) := (Complex.continuous_re.tendsto _).comp h360
    have hg1 : ((0 - 1 / s) / 12) = -(1 / (12 * s)) := by
      field_simp
      ring
    have hg2 : ((0 - 1 / s ^ 3) / 360) = -(1 / (360 * s ^ 3)) := by
      field_simp
      ring
    rw [hg1] at h12r
    rw [hg2] at h360r
    have hfin := h12r.neg.add h360r
    rw [Complex.neg_re, Complex.neg_re] at hfin
    rw [hf5]
    convert hfin using 1
    ring
  have hF6 : Tendsto f6 atTop
      (𝓝 (-(1 / 4) * (∫ x : ℝ in Set.Ioi 0,
        (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re)) := by
    have hb : Tendsto (fun n : ℕ => (((n + 1 : ℕ)) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hint := intervalIntegral_tendsto_integral_Ioi (f := fun x : ℝ =>
        (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)) (0 : ℝ)
      (LeanLab.RamareSaouter2003.Stirling518.fourth_kernel_integrable s hre.le him) hb
    have h5 : Tendsto (fun n : ℕ => (∫ x : ℝ in (0 : ℝ)..(((n + 1 : ℕ)) : ℝ),
        (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re) atTop
        (𝓝 ((∫ x : ℝ in Set.Ioi 0,
          (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re)) :=
      (Complex.continuous_re.tendsto _).comp hint
    have h6a := h5.div_const 4
    have h6 : Tendsto (fun n : ℕ => ((∫ x : ℝ in (0 : ℝ)..(((n + 1 : ℕ)) : ℝ),
        (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)) / 4).re) atTop
        (𝓝 ((∫ x : ℝ in Set.Ioi 0,
          (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re / 4)) := by
      refine Tendsto.congr' (Eventually.of_forall (fun n => ?_)) h6a
      have hns : Complex.normSq (4 : ℂ) = 16 := by
        rw [Complex.normSq_apply]
        norm_num
      simp only [Complex.div_re, hns, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        add_zero]
      norm_num
      ring
    have h7 : Tendsto (fun n : ℕ => -((∫ x : ℝ in (0 : ℝ)..(((n + 1 : ℕ)) : ℝ),
        (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)) / 4).re) atTop
        (𝓝 (-((∫ x : ℝ in Set.Ioi 0,
          (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re / 4))) := h6.neg
    have hv : -((∫ x : ℝ in Set.Ioi 0,
        (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re / 4) =
        -(1 / 4) * (∫ x : ℝ in Set.Ioi 0,
          (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re := by ring
    rw [hv] at h7
    rw [hf6]
    convert h7 using 1
  have key : ∀ n : ℕ, Real.log ‖Complex.GammaSeq s (n + 1)‖ =
      f1 n + f2 n + K + f5 n + f6 n := by
    intro n
    have hsum : (∑ k ∈ Finset.range (n + 2), Real.log ‖s + (k : ℂ)‖) =
        (∑ k ∈ Finset.range (n + 2), Complex.log (s + (k : ℂ))).re := by
      rw [Complex.re_sum]
      exact Finset.sum_congr rfl (fun k _ => (Complex.log_re _).symm)
    rw [log_norm_GammaSeq s hre n, hsum,
      LeanLab.RamareSaouter2003.Stirling518.finite_sum_log s him (n + 1)]
    have hhalf : ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_div]
      norm_num
    have hhalfre : ((1 / 2 : ℂ)).re = 1 / 2 := by rw [hhalf, Complex.ofReal_re]
    have hhalfim : ((1 / 2 : ℂ)).im = 0 := by rw [hhalf, Complex.ofReal_im]
    simp only [hf1, hf2, hf5, hf6, hK, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_natCast, Complex.ofReal_one,
      Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im,
      hhalfre, hhalfim, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  have hlim : Tendsto (fun n : ℕ => f1 n + f2 n + K + f5 n + f6 n) atTop
      (𝓝 (-s.re + Real.log (Real.sqrt (2 * π)) + K +
        ((1 / (12 * s)).re - (1 / (360 * s ^ 3)).re) +
        (-(1 / 4) * (∫ x : ℝ in Set.Ioi 0,
          (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re))) := by
    have h1 : Tendsto f1 atTop (𝓝 (-s.re)) := hA.neg
    have hr : Tendsto (fun n : ℕ => f1 n + f2 n + K) atTop
        (𝓝 (-s.re + Real.log (Real.sqrt (2 * π)) + K)) :=
      (h1.add hB).add tendsto_const_nhds
    exact ((hr.add hE).add hF6)
  have hcongr := hlim.congr' (Eventually.of_forall fun n => (key n).symm)
  rw [tendsto_nhds_unique hnorm hcongr]
  have hlog : Real.log (Real.sqrt (2 * π)) = (1 / 2) * Real.log (2 * π) := by
    rw [Real.log_sqrt (by positivity)]
    ring
  have hKv : K = (s.re - 1 / 2) * Real.log ‖s‖ - s.im * s.arg := by
    rw [hK]
    have h' : ((s - (1 / 2 : ℂ)) * Complex.log s - s).re =
        (s.re - 1 / 2) * Real.log ‖s‖ - s.im * s.arg - s.re := by
      rw [Complex.sub_re, Complex.mul_re, Complex.log_re, Complex.log_im]
      have hre' : (s - (1 / 2 : ℂ)).re = s.re - 1 / 2 := by simp
      have him' : (s - (1 / 2 : ℂ)).im = s.im := by simp
      rw [hre', him']
    rw [h']
    ring
  rw [hlog, hKv]
  ring


private lemma abs_bernoulliFun_four_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |bernoulliFun 4 r| ≤ 1 := by
  have h3 : _root_.bernoulli 3 = (0 : ℚ) := by decide +kernel
  have h4 : _root_.bernoulli 4 = (-1 / 30 : ℚ) := by decide +kernel
  have he : bernoulliFun 4 r = (r * (1 - r)) ^ 2 - 1 / 30 := by
    norm_num [bernoulliFun, Polynomial.bernoulli, Finset.sum_range_succ, h3, h4, Nat.choose]
    ring
  rw [he, abs_le]
  have hq0 : 0 ≤ r * (1 - r) := by nlinarith
  have hq1 : r * (1 - r) ≤ 1 / 4 := by nlinarith [sq_nonneg (r - 1 / 2)]
  constructor
  · nlinarith [sq_nonneg (r * (1 - r))]
  · nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]

set_option maxHeartbeats 2000000 in
private lemma integral_kernel_bound {s : ℂ} (hre : 0 ≤ s.re) (him : 0 < s.im) :
    -(1 / 4) * (∫ x : ℝ in Set.Ioi 0,
        (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re ≤ 1 / (3 * s.im ^ 3) := by
  have ht : 0 < s.im := him
  have hI := LeanLab.RamareSaouter2003.Stirling518.fourth_kernel_integrable s hre him
  have hpt : ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖(((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)‖ ≤ 4 * (1 / (x + s.im) ^ 4) := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hB := abs_bernoulliFun_four_le (Int.fract_nonneg x) (Int.fract_lt_one x).le
    have hne : s + (x : ℂ) ≠ 0 := by
      intro h
      have him0 := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.zero_im] at him0
      linarith
    have hsq : ‖s + (x : ℂ)‖ ^ 2 = (s.re + x) ^ 2 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im]
      ring
    have h1 : x ^ 2 + s.im ^ 2 ≤ ‖s + (x : ℂ)‖ ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg s.re, mul_nonneg hre hx0]
    have h2 : (x + s.im) ^ 2 ≤ 2 * (x ^ 2 + s.im ^ 2) := by
      nlinarith [sq_nonneg (x - s.im)]
    have hxpos : (0 : ℝ) < x + s.im := by linarith
    have h4 : (x + s.im) ^ 4 ≤ 4 * ‖s + (x : ℂ)‖ ^ 4 := by
      have h3 : ((x + s.im) ^ 2) ^ 2 ≤ (2 * (x ^ 2 + s.im ^ 2)) ^ 2 := by
        nlinarith [h2, sq_nonneg (x + s.im), sq_nonneg (x ^ 2 + s.im ^ 2)]
      have h5 : (2 * (x ^ 2 + s.im ^ 2)) ^ 2 ≤ 4 * (‖s + (x : ℂ)‖ ^ 2) ^ 2 := by
        nlinarith [h1, sq_nonneg (x ^ 2 + s.im ^ 2), sq_nonneg ‖s + (x : ℂ)‖]
      nlinarith [h3, h5]
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hm : |bernoulliFun 4 (Int.fract x)| * (x + s.im) ^ 4 ≤ 4 * ‖s + (x : ℂ)‖ ^ 4 := by
      have h1 : |bernoulliFun 4 (Int.fract x)| * (x + s.im) ^ 4 ≤ 1 * (x + s.im) ^ 4 :=
        mul_le_mul_of_nonneg_right hB (pow_nonneg hxpos.le 4)
      nlinarith [h1, h4]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖s + (x : ℂ)‖ ^ 4)]
    have heq2 : 4 * (1 / (x + s.im) ^ 4) * ‖s + (x : ℂ)‖ ^ 4 =
        4 * ‖s + (x : ℂ)‖ ^ 4 / (x + s.im) ^ 4 := by ring
    rw [heq2, le_div_iff₀ (by positivity : (0:ℝ) < (x + s.im) ^ 4)]
    linarith [hm]
  have hInt1 : IntegrableOn
      (fun x : ℝ => ‖(((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)‖) (Set.Ioi 0) :=
    hI.norm
  have hbase : IntegrableOn (fun x : ℝ => 1 / (x + s.im) ^ 4) (Set.Ioi 0) :=
    LeanLab.RamareSaouter2003.Stirling518.integrable_shifted_four s.im ht
  have hInt2 : IntegrableOn (fun x : ℝ => 4 * (1 / (x + s.im) ^ 4)) (Set.Ioi 0) :=
    hbase.const_mul 4
  have hmono := setIntegral_mono_on hInt1 hInt2 measurableSet_Ioi hpt
  have hval : (∫ x : ℝ in Set.Ioi 0, 1 / (x + s.im) ^ 4) = 1 / (3 * s.im ^ 3) := by
    have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun y : ℝ => -(1 / (y + s.im) ^ 3) / 3) (1 / (x + s.im) ^ 4) x := by
      intro x hx
      have hxy : 0 < x + s.im := by
        have := Set.mem_Ici.mp hx
        linarith
      have hn : (x + s.im) ^ 3 ≠ 0 := pow_ne_zero 3 hxy.ne'
      convert (((((hasDerivAt_id x).add_const s.im).pow 3).inv hn).neg.div_const 3) using 1
      · ext z; simp
      · simp only [Pi.pow_apply, id_eq]
        field_simp
        ring
    have hlim : Tendsto (fun x : ℝ => -(1 / (x + s.im) ^ 3) / 3) atTop (𝓝 0) := by
      have htend : Tendsto (fun x : ℝ => (x + s.im) ^ 3) atTop atTop :=
        (tendsto_pow_atTop (by decide : (3:ℕ) ≠ 0)).comp
          (tendsto_atTop_add_const_right _ s.im tendsto_id)
      simpa only [one_div, neg_zero, zero_div, Pi.inv_apply] using
        htend.inv_tendsto_atTop.neg.div_const 3
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hbase hlim]
    simp only [zero_sub, neg_neg]
    field_simp
    ring
  rw [integral_const_mul, hval] at hmono
  have hnorm : ‖∫ x : ℝ in Set.Ioi 0,
      (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)‖ ≤ 4 * (1 / (3 * s.im ^ 3)) := by
    refine le_trans ?_ hmono
    have h := norm_integral_le_integral_norm (fun x : ℝ =>
      (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4))
      (μ := volume.restrict (Set.Ioi 0))
    simpa using h
  have hfin : -(1 / 4) * (∫ x : ℝ in Set.Ioi 0,
      (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re ≤
        (1 / 4) * (4 * (1 / (3 * s.im ^ 3))) := by
    have h1 : -(∫ x : ℝ in Set.Ioi 0,
        (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re ≤
          ‖∫ x : ℝ in Set.Ioi 0, (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)‖ := by
      have h := Complex.re_le_norm (-(∫ x : ℝ in Set.Ioi 0,
        (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)))
      simpa using h
    linarith [h1, hnorm]
  calc -(1 / 4) * (∫ x : ℝ in Set.Ioi 0,
        (((bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) / (s + x) ^ 4)).re
      ≤ (1 / 4) * (4 * (1 / (3 * s.im ^ 3))) := hfin
    _ = 1 / (3 * s.im ^ 3) := by ring

set_option maxHeartbeats 4000000 in
private lemma log_Gamma_bound {a t : ℝ} (ha : a ∈ Set.Icc (1 : ℝ) (3 / 2)) (ht : 50 ≤ t) :
    Real.log ‖Complex.Gamma ((a : ℂ) + t * Complex.I)‖ ≤
      (1 / 2) * Real.log (2 * π) + (a - 1 / 2) * Real.log t - π * t / 2 +
        Real.log (1 + 1 / (4 * t ^ 2)) + Real.log (1 + 1 / (8 * t ^ 2)) := by
  have ht0 : 0 < t := by linarith
  have htne : t ≠ 0 := ht0.ne'
  have ha1 : 1 ≤ a := ha.1
  have ha2 : a ≤ 3 / 2 := ha.2
  set s : ℂ := (a : ℂ) + t * Complex.I with hs
  have hsre : s.re = a := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hre : 0 < s.re := by rw [hsre]; linarith
  have him : 0 < s.im := by rw [hsim]; linarith
  have hid := log_norm_Gamma_stirling hre him
  rw [hsre, hsim] at hid
  have hsne : s ≠ 0 := by intro h; rw [h] at him; simp at him
  have hsq : ‖s‖ ^ 2 = a ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hsre, hsim]
    ring
  have hlognorm : Real.log ‖s‖ ≤ Real.log t + a ^ 2 / (2 * t ^ 2) := by
    have hsqrt : ‖s‖ = Real.sqrt (a ^ 2 + t ^ 2) := by
      rw [← hsq, Real.sqrt_sq (norm_nonneg s)]
    rw [hsqrt, Real.log_sqrt (by positivity)]
    have hfac : a ^ 2 + t ^ 2 = t ^ 2 * (1 + a ^ 2 / t ^ 2) := by
      field_simp
      ring
    rw [hfac, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hl := log_le_self_add (u := a ^ 2 / t ^ 2) (by positivity)
    have heq : a ^ 2 / (2 * t ^ 2) = (a ^ 2 / t ^ 2) / 2 := by
      field_simp
    rw [heq]
    push_cast
    linarith
  have hB1 : (a - 1 / 2) * Real.log ‖s‖ ≤
      (a - 1 / 2) * Real.log t + (a ^ 3 / 2 - a ^ 2 / 4) / t ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlognorm (by linarith : (0:ℝ) ≤ a - 1 / 2)
    have he : (a - 1 / 2) * (a ^ 2 / (2 * t ^ 2)) = (a ^ 3 / 2 - a ^ 2 / 4) / t ^ 2 := by
      field_simp
      ring
    calc (a - 1 / 2) * Real.log ‖s‖ ≤ (a - 1 / 2) * (Real.log t + a ^ 2 / (2 * t ^ 2)) := h
      _ = (a - 1 / 2) * Real.log t + (a ^ 3 / 2 - a ^ 2 / 4) / t ^ 2 := by rw [mul_add, he]
  have hB2 : -t * s.arg ≤ -π * t / 2 + a - a ^ 3 / (3 * t ^ 2) + a ^ 5 / t ^ 4 := by
    have harg := LeanLab.RamareSaouter2003.Stirling518.arg_upper_half_plane s hre.le him
    rw [hsre, hsim] at harg
    have harith : -t * (π / 2 - Real.arctan (a / t)) =
        -π * t / 2 + t * Real.arctan (a / t) := by ring
    rw [harg, harith]
    have hT := arctan_le_taylor (x := a / t) (by positivity)
    have hexp : t * (a / t - (a / t) ^ 3 / 3 + (a / t) ^ 5) =
        a - a ^ 3 / (3 * t ^ 2) + a ^ 5 / t ^ 4 := by
      field_simp
      try ring
    linarith [mul_le_mul_of_nonneg_left hT ht0.le, hexp]
  have hC : (1 / (12 * s)).re ≤ a / (12 * t ^ 2) := by
    have hre12 : (1 / (12 * s)).re = a / (12 * (a ^ 2 + t ^ 2)) := by
      rw [one_div, Complex.inv_re]
      have h1 : (12 * s).re = 12 * a := by
        rw [Complex.mul_re]
        simp [hsre, hsim]
      have h2 : Complex.normSq (12 * s) = 144 * Complex.normSq s := by
        rw [Complex.normSq_mul]
        norm_num
      have h3 : Complex.normSq s = a ^ 2 + t ^ 2 := by
        rw [Complex.normSq_apply, hsre, hsim]
        ring
      rw [h1, h2, h3]
      field_simp
      ring
    rw [hre12]
    have h1 : (0 : ℝ) < 12 * t ^ 2 := by positivity
    have h2 : 12 * t ^ 2 ≤ 12 * (a ^ 2 + t ^ 2) := by nlinarith [sq_nonneg a]
    have h3 : (0 : ℝ) ≤ a := by linarith
    exact div_le_div_of_nonneg_left h3 h1 h2
  have hD : -(1 / (360 * s ^ 3)).re ≤ 1 / (360 * t ^ 3) := by
    have hnormval : ‖(1 : ℂ) / (360 * s ^ 3)‖ = 1 / (360 * ‖s‖ ^ 3) := by
      rw [norm_div, norm_mul, norm_pow]
      simp
    have hnorm : ‖(1 : ℂ) / (360 * s ^ 3)‖ ≤ 1 / (360 * t ^ 3) := by
      rw [hnormval]
      have htle : t ≤ ‖s‖ := by
        have h : t ^ 2 ≤ ‖s‖ ^ 2 := by
          rw [hsq]
          nlinarith [sq_nonneg a]
        nlinarith [h, norm_nonneg s, ht0]
      have hcube : t ^ 3 ≤ ‖s‖ ^ 3 := by nlinarith [htle, norm_nonneg s, ht0]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hcube])
    have h3 : -((1 : ℂ) / (360 * s ^ 3)).re ≤ ‖(1 : ℂ) / (360 * s ^ 3)‖ := by
      have h := Complex.re_le_norm (-((1 : ℂ) / (360 * s ^ 3)))
      simpa using h
    linarith [h3, hnorm]
  have hE := integral_kernel_bound hre.le him
  rw [hsim] at hE
  have hlog4 : 1 / (4 * t ^ 2) - 1 / (16 * t ^ 4) ≤ Real.log (1 + 1 / (4 * t ^ 2)) := by
    have h := neg_log_le (u := 1 / (4 * t ^ 2)) (by positivity)
    have he : (1 / (4 * t ^ 2)) ^ 2 = 1 / (16 * t ^ 4) := by
      rw [div_pow, mul_pow]
      norm_num
      ring
    linarith
  have hlog8 : 1 / (8 * t ^ 2) - 1 / (64 * t ^ 4) ≤ Real.log (1 + 1 / (8 * t ^ 2)) := by
    have h := neg_log_le (u := 1 / (8 * t ^ 2)) (by positivity)
    have he : (1 / (8 * t ^ 2)) ^ 2 = 1 / (64 * t ^ 4) := by
      rw [div_pow, mul_pow]
      norm_num
      ring
    linarith
  have hkey : (a ^ 3 / 2 - a ^ 2 / 4) / t ^ 2 - a ^ 3 / (3 * t ^ 2) + a / (12 * t ^ 2) +
      a ^ 5 / t ^ 4 + 1 / (360 * t ^ 3) + 1 / (3 * t ^ 3) ≤
        1 / (4 * t ^ 2) - 1 / (16 * t ^ 4) + 1 / (8 * t ^ 2) - 1 / (64 * t ^ 4) := by
    have hbig : a ^ 3 * t ^ 2 / 6 - a ^ 2 * t ^ 2 / 4 + a * t ^ 2 / 12 - 3 * t ^ 2 / 8 +
        a ^ 5 + (121 / 360) * t + 5 / 64 ≤ 0 := by
      have ha5 : a ^ 5 ≤ 243 / 32 := by
        have h := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ a) ha2 5
        norm_num at h
        linarith
      have hρ : a ^ 3 / 6 - a ^ 2 / 4 + a / 12 - 3 / 8 ≤ -1 / 4 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 - 2 * a) (by positivity : (0:ℝ) ≤ 2 * a ^ 2 + 1)]
      have h1 : t ^ 2 * (a ^ 3 / 6 - a ^ 2 / 4 + a / 12 - 3 / 8) ≤ t ^ 2 * (-1 / 4) :=
        mul_le_mul_of_nonneg_left hρ (sq_nonneg t)
      have ht2 : (2500 : ℝ) ≤ t ^ 2 := by nlinarith [ht, sq_nonneg (t - 50)]
      nlinarith [h1, ha5, ht, ht2]
    have ht4 : (0 : ℝ) < t ^ 4 := by positivity
    have heq : (a ^ 3 / 2 - a ^ 2 / 4) / t ^ 2 - a ^ 3 / (3 * t ^ 2) + a / (12 * t ^ 2) +
        a ^ 5 / t ^ 4 + 1 / (360 * t ^ 3) + 1 / (3 * t ^ 3) -
          (1 / (4 * t ^ 2) - 1 / (16 * t ^ 4) + 1 / (8 * t ^ 2) - 1 / (64 * t ^ 4)) =
        (a ^ 3 * t ^ 2 / 6 - a ^ 2 * t ^ 2 / 4 + a * t ^ 2 / 12 - 3 * t ^ 2 / 8 +
          a ^ 5 + (121 / 360) * t + 5 / 64) / t ^ 4 := by
      field_simp
      ring
    have hle : (a ^ 3 / 2 - a ^ 2 / 4) / t ^ 2 - a ^ 3 / (3 * t ^ 2) + a / (12 * t ^ 2) +
        a ^ 5 / t ^ 4 + 1 / (360 * t ^ 3) + 1 / (3 * t ^ 3) -
          (1 / (4 * t ^ 2) - 1 / (16 * t ^ 4) + 1 / (8 * t ^ 2) - 1 / (64 * t ^ 4)) ≤ 0 := by
      rw [heq]
      exact div_nonpos_of_nonpos_of_nonneg hbig ht4.le
    linarith [hle]
  linarith [hid, hB1, hB2, hC, hD, hE, hlog4, hlog8, hkey]

end GammaGrowthAux

/-- Backlund p. 369 display 75, the exact functional equation multiplier. -/
noncomputable def functionalMultiplier (s : ℂ) : ℂ :=
  2 * (2 * π) ^ (-s) * Complex.Gamma s * Complex.cos (π * s / 2)

/-- Backlund p. 369 display 75, the reflected zeta norm identity. -/
theorem reflection_norm_identity (a t : ℝ) (ht : 0 < t) :
    ‖riemannZeta (((1 - a : ℝ) : ℂ) + t * I)‖ =
      ‖functionalMultiplier ((a : ℂ) - t * I)‖ *
        ‖riemannZeta ((a : ℂ) + t * I)‖ := by
  let s : ℂ := (a : ℂ) - t * I
  have hs : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have hi := congrArg Complex.im h
    simp [s] at hi
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp [s] at hi
    linarith
  have he : 1 - s = (((1 - a : ℝ) : ℂ) + t * I) := by dsimp [s]; push_cast; ring
  have hc : s = starRingEnd ℂ ((a : ℂ) + t * I) := by simp [s, map_add, map_mul, sub_eq_add_neg]
  have h := riemannZeta_one_sub hs hs1
  rw [he] at h
  rw [h, norm_mul]
  change ‖functionalMultiplier s‖ * ‖riemannZeta s‖ = _
  have hz : ‖riemannZeta s‖ = ‖riemannZeta ((a : ℂ) + t * I)‖ := by
    rw [hc, riemannZeta_conj, Complex.norm_conj]
  rw [hz]

/-- Backlund p. 369, the elementary three-factor budget in display 76. -/
theorem multiplier_error_budget (t : ℝ) (ht : 50 ≤ t) :
    (1 + 1 / (4 * t ^ 2)) * (1 + 1 / (8 * t ^ 2)) *
      (1 + 1 / (16 * t ^ 2)) ≤ 1 + 1 / (2 * t ^ 2) := by
  let x : ℝ := 1 / t ^ 2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxu : x ≤ 1 / 2500 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < t ^ 2)).mpr
    nlinarith
  have he4 : 1 / (4 * t ^ 2) = x / 4 := by dsimp [x]; ring
  have he8 : 1 / (8 * t ^ 2) = x / 8 := by dsimp [x]; ring
  have he16 : 1 / (16 * t ^ 2) = x / 16 := by dsimp [x]; ring
  have he2 : 1 / (2 * t ^ 2) = x / 2 := by dsimp [x]; ring
  rw [he4, he8, he16, he2]
  have hxx : x ^ 2 ≤ x / 2500 := by nlinarith
  have hxxx : x ^ 3 ≤ x ^ 2 / 2500 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hxu)]
  nlinarith [pow_nonneg hx 3]

/-- Backlund p. 369, the exponentially small cosine error has a rational majorant. -/
theorem exp_cosine_error (t : ℝ) (ht : 50 ≤ t) :
    Real.exp (-π * t) ≤ 1 / (16 * t ^ 2) := by
  have htpos : 0 < t := by linarith
  have hp : 3 * t ≤ π * t := mul_le_mul_of_nonneg_right Real.pi_gt_three.le htpos.le
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3 * t) hp 3
  have h3 := Real.pow_div_factorial_le_exp (π * t) (by positivity : (0 : ℝ) ≤ π * t) 3
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at h3
  have ht3 : 50 * t ^ 2 ≤ t ^ 3 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht)]
  have he : 16 * t ^ 2 ≤ Real.exp (π * t) := by nlinarith
  rw [show -π * t = -(π * t) by ring, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 16 * t ^ 2) he

/-- Backlund p. 369 before display 75, the complex cosine factor bound. -/
theorem cosine_factor_bound (a t : ℝ) (ht : 50 ≤ t) :
    ‖Complex.cos (π * ((a : ℂ) - t * I) / 2)‖ ≤
      Real.exp (π * t / 2) / 2 * (1 + 1 / (16 * t ^ 2)) := by
  let z : ℂ := π * ((a : ℂ) - t * I) / 2
  have hpos : (z * I).re = π * t / 2 := by simp [z, Complex.mul_re, Complex.mul_im]; ring
  have hneg : (-z * I).re = -(π * t / 2) := by simp [z, Complex.mul_re, Complex.mul_im]; ring
  have h := norm_add_le (Complex.exp (z * I)) (Complex.exp (-z * I))
  rw [Complex.norm_exp, Complex.norm_exp, hpos, hneg] at h
  have he : Real.exp (-(π * t / 2)) = Real.exp (π * t / 2) * Real.exp (-π * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  have hsmall := exp_cosine_error t ht
  change ‖Complex.cos z‖ ≤ _
  rw [Complex.cos, norm_div]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (Real.exp (π * t / 2) + Real.exp (π * t / 2) * Real.exp (-π * t)) / 2 :=
      div_le_div_of_nonneg_right h (by norm_num)
    _ ≤ (Real.exp (π * t / 2) + Real.exp (π * t / 2) * (1 / (16 * t ^ 2))) / 2 := by gcongr
    _ = _ := by ring

/-- LEAF. Backlund pp. 368 and 369 display 74 and the Gamma recurrence.
The shifted real Stirling remainder gives the factor one plus one over four t squared.
The recurrence contributes the factor one plus one over eight t squared.
No cosine, zeta value or functional equation occurs in this leaf. -/
theorem gamma74_upper (a t : ℝ) (ha : a ∈ Set.Icc (1 : ℝ) (3 / 2)) (ht : 50 ≤ t) :
    ‖Complex.Gamma ((a : ℂ) - t * I)‖ ≤
      Real.sqrt (2 * π) * t ^ (a - 1 / 2) * Real.exp (-π * t / 2) *
        (1 + 1 / (4 * t ^ 2)) * (1 + 1 / (8 * t ^ 2)) := by
  have ht0 : 0 < t := by linarith
  have hconj : ((a : ℂ) - t * Complex.I) = starRingEnd ℂ ((a : ℂ) + t * Complex.I) := by
    simp
    ring
  rw [hconj, Complex.Gamma_conj, Complex.norm_conj]
  have hne : Complex.Gamma ((a : ℂ) + t * Complex.I) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linarith [ha.1]
  have hpos : 0 < ‖Complex.Gamma ((a : ℂ) + t * Complex.I)‖ := norm_pos_iff.mpr hne
  have hexp := Real.exp_le_exp.mpr (log_Gamma_bound ha ht)
  rw [Real.exp_log hpos] at hexp
  have hrhs : Real.exp ((1 / 2) * Real.log (2 * π) + (a - 1 / 2) * Real.log t - π * t / 2 +
      Real.log (1 + 1 / (4 * t ^ 2)) + Real.log (1 + 1 / (8 * t ^ 2))) =
      Real.sqrt (2 * π) * t ^ (a - 1 / 2) * Real.exp (-π * t / 2) *
        (1 + 1 / (4 * t ^ 2)) * (1 + 1 / (8 * t ^ 2)) := by
    have hsplit : (1 / 2) * Real.log (2 * π) + (a - 1 / 2) * Real.log t - π * t / 2 +
        Real.log (1 + 1 / (4 * t ^ 2)) + Real.log (1 + 1 / (8 * t ^ 2))
        = (1 / 2) * Real.log (2 * π) + ((a - 1 / 2) * Real.log t +
            (-(π * t / 2) + (Real.log (1 + 1 / (4 * t ^ 2)) + Real.log (1 + 1 / (8 * t ^ 2))))) := by
      ring
    rw [hsplit, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
    have hA : Real.exp ((1 / 2) * Real.log (2 * π)) = Real.sqrt (2 * π) := by
      have h1 : (1 / 2) * Real.log (2 * π) = Real.log (Real.sqrt (2 * π)) := by
        rw [Real.log_sqrt (by positivity)]
        ring
      rw [h1, Real.exp_log (by positivity)]
    have hB : Real.exp ((a - 1 / 2) * Real.log t) = t ^ (a - 1 / 2) := by
      rw [Real.rpow_def_of_pos ht0]
      congr 1
      ring
    have hC' : Real.exp (-(π * t / 2)) = Real.exp (-π * t / 2) := by
      congr 1
      ring
    have hD' : Real.exp (Real.log (1 + 1 / (4 * t ^ 2))) = 1 + 1 / (4 * t ^ 2) :=
      Real.exp_log (by positivity)
    have hE' : Real.exp (Real.log (1 + 1 / (8 * t ^ 2))) = 1 + 1 / (8 * t ^ 2) :=
      Real.exp_log (by positivity)
    rw [hA, hB, hC', hD', hE']
    ring
  rw [hrhs] at hexp
  exact hexp

/-- Backlund pp. 368 and 369 displays 74 through 76.
CONDITIONAL ON gamma74_upper.
Bound only the explicit Gamma and cosine multiplier.
The real Stirling remainder at s minus one is display 74.
The recurrence, cosine formula and scalar error product give this bound.
No zeta growth estimate occurs in this leaf. -/
theorem multiplier76_bound (a t : ℝ) (ha : a ∈ Set.Icc (1 : ℝ) (3 / 2)) (ht : 50 ≤ t) :
    ‖functionalMultiplier ((a : ℂ) - t * I)‖ ≤
      (t / (2 * π)) ^ (a - 1 / 2) * (1 + 1 / (2 * t ^ 2)) := by
  have htpos : 0 < t := by linarith
  have hb : 0 < 2 * π := by positivity
  have hpow : ‖(2 * π : ℂ) ^ (-((a : ℂ) - t * I))‖ = (2 * π : ℝ) ^ (-a) := by
    have he : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_cpow_eq_rpow_re_of_pos hb]
    simp
  have hscale : (2 * π : ℝ) ^ (-a) * Real.sqrt (2 * π) * t ^ (a - 1 / 2) =
      (t / (2 * π)) ^ (a - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb]
    rw [show -a + 1 / 2 = -(a - 1 / 2) by ring, Real.rpow_neg hb.le,
      Real.div_rpow htpos.le hb.le]
    ring
  have he : Real.exp (-π * t / 2) * Real.exp (π * t / 2) = 1 := by
    rw [← Real.exp_add, show -π * t / 2 + π * t / 2 = 0 by ring, Real.exp_zero]
  have hg := gamma74_upper a t ha ht
  have hc := cosine_factor_bound a t ht
  unfold functionalMultiplier
  simp only [norm_mul, Complex.norm_ofNat]
  rw [hpow]
  calc
    _ ≤ 2 * (2 * π : ℝ) ^ (-a) *
        (Real.sqrt (2 * π) * t ^ (a - 1 / 2) * Real.exp (-π * t / 2) *
          (1 + 1 / (4 * t ^ 2)) * (1 + 1 / (8 * t ^ 2))) *
        (Real.exp (π * t / 2) / 2 * (1 + 1 / (16 * t ^ 2))) := by gcongr
    _ = ((2 * π : ℝ) ^ (-a) * Real.sqrt (2 * π) * t ^ (a - 1 / 2)) *
        (Real.exp (-π * t / 2) * Real.exp (π * t / 2)) *
        ((1 + 1 / (4 * t ^ 2)) * (1 + 1 / (8 * t ^ 2)) * (1 + 1 / (16 * t ^ 2))) := by ring
    _ = (t / (2 * π)) ^ (a - 1 / 2) *
        ((1 + 1 / (4 * t ^ 2)) * (1 + 1 / (8 * t ^ 2)) * (1 + 1 / (16 * t ^ 2))) := by rw [hscale, he, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left (multiplier_error_budget t ht) (by positivity)

/-- Backlund p. 369 display 76, the exact original reflected norm comparison.
CONDITIONAL ON multiplier76_bound. -/
theorem reflection76 (σ t : ℝ) (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) 0) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * π)) ^ (1 / 2 - σ) * (1 + 1 / (2 * t ^ 2)) *
        ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ := by
  have ha : 1 - σ ∈ Set.Icc (1 : ℝ) (3 / 2) := by
    constructor <;> linarith [hσ.1, hσ.2]
  have h := multiplier76_bound (1 - σ) t ha ht
  have he : 1 - σ - 1 / 2 = 1 / 2 - σ := by ring
  rw [he] at h
  have hi := reflection_norm_identity (1 - σ) t (by linarith)
  have hs : 1 - (1 - σ) = σ := by ring
  rw [hs] at hi
  rw [hi]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

end LeanLab.RamareSaouter2003.Decomp563b

#print axioms LeanLab.RamareSaouter2003.Decomp563b.functionalMultiplier
#print axioms LeanLab.RamareSaouter2003.Decomp563b.reflection_norm_identity
#print axioms LeanLab.RamareSaouter2003.Decomp563b.multiplier_error_budget
#print axioms LeanLab.RamareSaouter2003.Decomp563b.multiplier76_bound
#print axioms LeanLab.RamareSaouter2003.Decomp563b.reflection76

#print axioms LeanLab.RamareSaouter2003.Decomp563b.exp_cosine_error

#print axioms LeanLab.RamareSaouter2003.Decomp563b.cosine_factor_bound

#print axioms LeanLab.RamareSaouter2003.Decomp563b.gamma74_upper
