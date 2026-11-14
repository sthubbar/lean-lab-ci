/-
Jia 1996 page 270, polynomial integration for Omega11.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Numeric11Cert566

namespace LeanLab.Languasco2004.Numeric11_566
open Real Set intervalIntegral Kernel11_566 Numeric548 Numeric30_548 MovingIntegral548
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Page 270: the first inner integral has its exact printed logarithmic integrand. -/
def innerLog11 (t : ℝ) : ℝ :=
  ∫ u in (17 / 30 - 6 / 5 * t)..((1 - t) / 3),
    (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u))

/-- Page 270: the second inner integral has its exact printed rational integrand. -/
def innerRat11 (t : ℝ) : ℝ :=
  ∫ u in ((1 - t) / 3)..(7 / 24 - t / 8), 1 / (t * u * (1 - t - u))

/-- Page 270: the two numerical integrals before the prime transfer. -/
def model11 : ℝ :=
  (∫ t in (17 / 63 : ℝ)..(17 / 57), innerLog11 t) +
    (∫ t in (17 / 63 : ℝ)..(17 / 57), innerRat11 t)

/-- LEAF. Page 270 support: both exact inner integrals vary continuously. -/
theorem inner11_continuousOn :
    ContinuousOn innerLog11 (Icc (17 / 63) (17 / 57)) ∧
    ContinuousOn innerRat11 (Icc (17 / 63) (17 / 57)) := by
  let R := Icc (17 / 63 : ℝ) (17 / 57) ×ˢ Icc (119 / 570 : ℝ) (65 / 252)
  have ht (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.1 := by linarith [hz.1.1]
  have hu (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.2 := by linarith [hz.2.1]
  have hv (z : ℝ × ℝ) (hz : z ∈ R) : 0 < 1 - z.1 - z.2 := by
    linarith [hz.1.2, hz.2.2]
  have harg (z : ℝ × ℝ) (hz : z ∈ R) : 0 < (1 - z.1) / z.2 - 2 := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ (hu z hz)).mpr
    linarith [hz.1.2, hz.2.2]
  have hrat : ContinuousOn (fun z : ℝ × ℝ => (1 - z.1) / z.2 - 2) R :=
    ((continuousOn_const.sub continuous_fst.continuousOn).div continuous_snd.continuousOn
      (fun z hz => (hu z hz).ne')).sub continuousOn_const
  have hden : ContinuousOn (fun z : ℝ × ℝ => z.1 * z.2 * (1 - z.1 - z.2)) R := by fun_prop
  have hnz (z : ℝ × ℝ) (hz : z ∈ R) : z.1 * z.2 * (1 - z.1 - z.2) ≠ 0 :=
    (mul_pos (mul_pos (ht z hz) (hu z hz)) (hv z hz)).ne'
  have hlog : ContinuousOn (fun z : ℝ × ℝ =>
      (1 + Real.log ((1 - z.1) / z.2 - 2)) / (z.1 * z.2 * (1 - z.1 - z.2))) R :=
    (continuousOn_const.add (hrat.log (fun z hz => (harg z hz).ne'))).div hden hnz
  have hone : ContinuousOn (fun z : ℝ × ℝ => 1 / (z.1 * z.2 * (1 - z.1 - z.2))) R :=
    continuousOn_const.div hden hnz
  constructor
  · apply moving_integral_continuousOn
      (fun t u : ℝ => (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)))
      (17 / 63) (17 / 57) (119 / 570) (65 / 252)
      (fun t => 17 / 30 - 6 / 5 * t) (fun t => (1 - t) / 3)
      (by norm_num) (by norm_num) hlog (by fun_prop) (by fun_prop)
    intro t ht
    have := ht.1
    have := ht.2
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  · apply moving_integral_continuousOn
      (fun t u : ℝ => 1 / (t * u * (1 - t - u)))
      (17 / 63) (17 / 57) (119 / 570) (65 / 252)
      (fun t => (1 - t) / 3) (fun t => 7 / 24 - t / 8)
      (by norm_num) (by norm_num) hone (by fun_prop) (by fun_prop)
    intro t ht
    have := ht.1
    have := ht.2
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith

/-- Page 270 support: either polynomial inner integral is continuous for affine endpoints. -/
theorem polynomial_inner_continuous (P : ℝ → ℝ → ℝ)
    (hP : Continuous (Function.uncurry P)) (L U : ℝ → ℝ)
    (hL : Continuous L) (hU : Continuous U) :
    Continuous (fun t => ∫ u in L t..U t, P t u) := by
  have hIu := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hP hU
  have hIl := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hP hL
  have he : (fun t => ∫ u in L t..U t, P t u) = fun t =>
      (∫ u in (0 : ℝ)..U t, P t u) - (∫ u in (0 : ℝ)..L t, P t u) := by
    funext t
    exact (integral_interval_sub_left ((hP.uncurry_left t).intervalIntegrable _ _)
      ((hP.uncurry_left t).intervalIntegrable _ _)).symm
  rw [he]
  exact hIu.sub hIl

/-- LEAF. Page 270: the complete logarithmic integral exceeds its printed coefficient. -/
theorem logarithmic_integral_lower :
    (0.0126553 : ℝ) ≤ ∫ t in (17 / 63 : ℝ)..(17 / 57), innerLog11 t := by
  have hP : Continuous (Function.uncurry logPolynomial) := by
    unfold logPolynomial invPoly3 invPoly5 Midpoint566.invPoly1
    fun_prop
  have hi := polynomial_inner_continuous logPolynomial hP
    (fun t => 17 / 30 - 6 / 5 * t) (fun t => (1 - t) / 3) (by fun_prop) (by fun_prop)
  apply logPolynomial_integral.trans
  apply integral_mono_on (by norm_num : (17 / 63 : ℝ) ≤ 17 / 57)
    (hi.intervalIntegrable _ _) (inner11_continuousOn.1.intervalIntegrable_of_Icc (by norm_num))
  intro t ht
  have hab : 17 / 30 - 6 / 5 * t ≤ (1 - t) / 3 := by linarith [ht.1]
  have hr : IntervalIntegrable (fun u : ℝ =>
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)))
      MeasureTheory.volume (17 / 30 - 6 / 5 * t) ((1 - t) / 3) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    have hu (u : ℝ) (hu : u ∈ Icc (17 / 30 - 6 / 5 * t) ((1 - t) / 3)) : 0 < u := by
      linarith [ht.2, hu.1]
    have hv (u : ℝ) (hu : u ∈ Icc (17 / 30 - 6 / 5 * t) ((1 - t) / 3)) : 0 < 1 - t - u := by
      linarith [ht.2, hu.2]
    have harg (u : ℝ) (hu : u ∈ Icc (17 / 30 - 6 / 5 * t) ((1 - t) / 3)) :
        (1 - t) / u - 2 ≠ 0 := by
      have he : 0 < (1 - t) / u - 2 := by
        apply sub_pos.mpr
        apply (lt_div_iff₀ (by linarith [ht.2, hu.1] : (0 : ℝ) < u)).mpr
        linarith [ht.2, hu.2]
      exact he.ne'
    have hc : ContinuousOn (fun u : ℝ => (1 - t) / u - 2)
        (Icc (17 / 30 - 6 / 5 * t) ((1 - t) / 3)) :=
      (continuousOn_const.div continuousOn_id (fun u h => (hu u h).ne')).sub continuousOn_const
    exact (continuousOn_const.add (hc.log harg)).div (by fun_prop)
      (fun u h => (mul_pos (mul_pos (by linarith [ht.1]) (hu u h)) (hv u h)).ne')
  exact integral_mono_on hab ((hP.uncurry_left t).intervalIntegrable _ _) hr
    (fun u hu => logPolynomial_le t u ht.1 ht.2 hu.1 hu.2)

/-- Page 270: the complete rational integral exceeds its printed coefficient. -/
theorem rational_integral_lower :
    (0.01510605 : ℝ) ≤ ∫ t in (17 / 63 : ℝ)..(17 / 57), innerRat11 t := by
  have hP : Continuous (Function.uncurry ratPolynomial) := by
    unfold ratPolynomial invPoly5
    fun_prop
  have hi := polynomial_inner_continuous ratPolynomial hP
    (fun t => (1 - t) / 3) (fun t => 7 / 24 - t / 8) (by fun_prop) (by fun_prop)
  apply ratPolynomial_integral.trans
  apply integral_mono_on (by norm_num : (17 / 63 : ℝ) ≤ 17 / 57)
    (hi.intervalIntegrable _ _) (inner11_continuousOn.2.intervalIntegrable_of_Icc (by norm_num))
  intro t ht
  have hab : (1 - t) / 3 ≤ 7 / 24 - t / 8 := by linarith [ht.1]
  have hr := Integral548.rational_kernel_integrable t ((1 - t) / 3) (7 / 24 - t / 8)
    (by linarith [ht.1]) hab (by linarith [ht.2]) (by linarith [ht.2])
  exact integral_mono_on hab ((hP.uncurry_left t).intervalIntegrable _ _) hr
    (fun u hu => ratPolynomial_le t u ht.1 ht.2 hu.1 hu.2)

/-- Page 270: the two exact integrals leave room to absorb the analytic error. -/
theorem model11_lower : (0.02776135 : ℝ) ≤ model11 := by
  unfold model11
  linarith [logarithmic_integral_lower, rational_integral_lower]

/-- Page 270: in particular the complete numerical model reaches the printed coefficient. -/
theorem printed_coefficient_lower : (0.027761 : ℝ) < model11 := by
  linarith [model11_lower]

#print axioms inner11_continuousOn
#print axioms polynomial_inner_continuous
#print axioms logarithmic_integral_lower
#print axioms rational_integral_lower
#print axioms model11_lower
#print axioms printed_coefficient_lower

#print axioms logPolynomial_integral
#print axioms ratPolynomial_integral
end
end LeanLab.Languasco2004.Numeric11_566
