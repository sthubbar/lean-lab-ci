import LeanLab.RamareSaouter2003.Circle419

/-!
Rosser pp. 223 and 224 and Backlund pp. 354 to 361, displays 44 to 50.
The powered count inequality separates into a Backlund zero mass bound
and the already proved Mathlib Jensen formula.
The zero mass is defined from the actual auxiliary function and its divisor.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp419b
open Real Complex MeasureTheory Decomp359g
open scoped ComplexConjugate

/-- LEAF. Backlund p. 360 and Rosser pp. 223 and 224.
Both shifted zeta poles are outside the closed disk of radius 1.32. -/
theorem powered_analytic (T : ℝ) (hT : 1400 ≤ T) (N : ℕ) :
    AnalyticOnNhd ℂ (poweredZeta T N) (Metric.closedBall 0 |(1.32 : ℝ)|) := by
  intro z hz
  have hn : ‖z‖ ≤ (1.32 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right, abs_of_pos (by norm_num : (0 : ℝ) < 1.32)] using hz
  have hplus : z + 5 / 4 + T * I ≠ 1 := by
    intro hh
    have he := congrArg Complex.im hh
    have hab := Complex.abs_im_le_norm z
    simp only [Complex.add_im, Complex.div_ofNat_im, Complex.im_ofNat, zero_div,
      add_zero, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, zero_add, Complex.one_im] at he
    have hm : |z.im| = T := by rw [show z.im = -T by linarith, abs_neg, abs_of_nonneg (by linarith)]
    rw [hm] at hab
    linarith
  have hminus : z + 5 / 4 - T * I ≠ 1 := by
    intro hh
    have he := congrArg Complex.im hh
    have hab := Complex.abs_im_le_norm z
    simp only [Complex.sub_im, Complex.add_im, Complex.div_ofNat_im, Complex.im_ofNat,
      zero_div, add_zero, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, zero_add, Complex.one_im] at he
    have hm : |z.im| = T := by rw [show z.im = T by linarith, abs_of_nonneg (by linarith)]
    rw [hm] at hab
    linarith
  have hp : AnalyticAt ℂ (fun w : ℂ => riemannZeta (w + 5 / 4 + T * I)) z := by
    exact (analyticOn_riemannZeta _ hplus).comp (f := fun w : ℂ => w + 5 / 4 + T * I) (x := z)
      ((analyticAt_id.add analyticAt_const).add analyticAt_const)
  have hm : AnalyticAt ℂ (fun w : ℂ => riemannZeta (w + 5 / 4 - T * I)) z := by
    exact (analyticOn_riemannZeta _ hminus).comp (f := fun w : ℂ => w + 5 / 4 - T * I) (x := z)
      ((analyticAt_id.add analyticAt_const).sub analyticAt_const)
  exact (hp.pow N |>.add (hm.pow N)).div_const

/-- Backlund p. 360, Jensen's weighted zero mass for the actual powered G.
The divisor counts analytic multiplicities in the closed disk.
Boundary zeros contribute log one, hence zero. -/
noncomputable def zeroMass (T : ℝ) (N : ℕ) : ℝ :=
  ∑ᶠ z : ℂ, (MeromorphicOn.divisor (poweredZeta T N)
    (Metric.closedBall 0 |(1.32 : ℝ)|) z : ℝ) * Real.log (1.32 * ‖(0 : ℂ) - z‖⁻¹)

/-- LEAF. Backlund p. 360, Jensen's identity before the paired-zero estimate.
Mathlib supplies the exact formula, including possible boundary zeros. -/
theorem zeroMass_eq_average (T : ℝ) (hT : 1400 ≤ T) (N : ℕ)
    (hG : poweredZeta T N 0 ≠ 0) :
    zeroMass T N = circleAverage (fun z => Real.log ‖poweredZeta T N z‖) 0 1.32 -
      Real.log ‖poweredZeta T N 0‖ := by
  have h := (powered_analytic T hT N).circleAverage_log_norm (by norm_num) hG
  change _ = zeroMass T N + _ at h
  linarith

/-- LEAF. Rosser p. 224, conjugation of the actual symmetrized zeta powers. -/
theorem powered_conj (T : ℝ) (N : ℕ) (z : ℂ) :
    poweredZeta T N (conj z) = conj (poweredZeta T N z) := by
  have hq : (5 / 4 : ℂ) = ((5 / 4 : ℝ) : ℂ) := by norm_num
  have hp : conj (z + 5 / 4 + T * I) = conj z + 5 / 4 - T * I := by
    rw [hq]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    ring
  have hm : conj (z + 5 / 4 - T * I) = conj z + 5 / 4 + T * I := by
    rw [hq]
    simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    ring
  unfold poweredZeta
  simp only [map_div₀, map_add, map_pow, map_ofNat, ← riemannZeta_conj, hp, hm]
  ring

/-- LEAF. Backlund p. 360, symmetry reduces the full circle to a semicircle. -/
theorem average_eq_semicircle (T : ℝ) (hT : 1400 ≤ T) (N : ℕ) :
    circleAverage (fun z => Real.log ‖poweredZeta T N z‖) 0 1.32 =
      (∫ φ in (0 : ℝ)..π,
        Real.log ‖poweredZeta T N ((1.32 : ℂ) * Complex.exp (φ * I))‖) / π := by
  let F : ℝ → ℝ := fun φ => Real.log ‖poweredZeta T N (circleMap 0 1.32 φ)‖
  have heven (φ : ℝ) : F (-φ) = F φ := by
    dsimp only [F]
    rw [← conj_circleMap_zero, powered_conj, Complex.norm_conj]
  have hip : IntervalIntegrable F volume 0 π := by
    simpa only [F, circleMap, zero_add, Complex.ofReal_ofScientific] using
      Circle419.powered_log_integrable T hT N
  have hin : IntervalIntegrable F volume (-π) 0 := by
    have h := hip.symm.comp_sub_left 0
    simpa only [zero_sub, sub_zero, heven] using h
  have hi : (∫ φ in (-π)..0, F φ) = ∫ φ in (0 : ℝ)..π, F φ := by
    have h := intervalIntegral.integral_comp_sub_left F (a := -π) (b := 0) 0
    simpa only [zero_sub, neg_neg, sub_zero, heven] using h
  have h := circleAverage_eq_integral_add (f := fun z => Real.log ‖poweredZeta T N z‖)
    (c := 0) (R := 1.32) (-π)
  change _ = (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..(2 * π), F (θ + -π) at h
  rw [intervalIntegral.integral_comp_add_right F] at h
  simp only [zero_add] at h
  have hend : 2 * π + -π = π := by ring
  rw [hend] at h
  change _ = (2 * π)⁻¹ • ∫ φ in (-π)..π, F φ at h
  rw [← intervalIntegral.integral_add_adjacent_intervals hin hip, hi] at h
  rw [h]
  simp only [smul_eq_mul]
  have heq : (∫ φ in (0 : ℝ)..π,
      Real.log ‖poweredZeta T N ((1.32 : ℂ) * Complex.exp (φ * I))‖) =
        ∫ φ in (0 : ℝ)..π, F φ := by
    apply intervalIntegral.integral_congr
    intro φ _
    simp only [F, circleMap, zero_add, Complex.ofReal_ofScientific]
  rw [heq]
  ring

/-- LEAF. Backlund p. 360 after display 48, the paired zero distance estimate.
Two positive distances with product at most three quarters squared
contribute at least twice q to the Jensen zero mass. -/
theorem paired_log_weight (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a * b ≤ (3 / 4 : ℝ) ^ 2) :
    2 * Real.log (4 * 1.32 / 3) ≤ Real.log (1.32 / a) + Real.log (1.32 / b) := by
  have h := Real.log_le_log (mul_pos ha hb) hab
  rw [Real.log_mul ha.ne' hb.ne', Real.log_pow] at h
  rw [show (4 * 1.32 / 3 : ℝ) = 1.32 / (3 / 4) by norm_num,
    Real.log_div (by norm_num : (1.32 : ℝ) ≠ 0) (by norm_num : (3 / 4 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (1.32 : ℝ) ≠ 0) ha.ne',
    Real.log_div (by norm_num : (1.32 : ℝ) ≠ 0) hb.ne']
  linarith

/-- LEAF. Rosser pp. 223 and 224, Backlund pp. 354 to 360, displays 44 to 48.
The argument principle and paired real zeros bound the actual count error
by the weighted zero mass. There is no circle integral in this leaf.
The constant k is independent of the natural power N. -/
theorem backlund_zero_mass_count (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ N : ℕ, 0 < N → poweredZeta T N 0 ≠ 0 →
      |L1Zeta.NZr T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
        zeroMass T N / (2 * Real.log (4 * 1.32 / 3) * N) +
          1 / 2 + 4 / (π * T) + |gammaRemainder T| / π + k / N := by
  sorry

/-- Rosser pp. 223 and 224, exactly the original powered_jensen_count target.
CONDITIONAL ON backlund_zero_mass_count. Jensen and conjugation are proved. -/
theorem powered_jensen_count (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ N : ℕ, 0 < N → poweredZeta T N 0 ≠ 0 →
      |L1Zeta.NZr T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
        jensenFunctional T N + k / N := by
  obtain ⟨k, hk, hb⟩ := backlund_zero_mass_count A T hA hFA hT
  refine ⟨k, hk, fun N hN hG => ?_⟩
  have hmass := zeroMass_eq_average T (hA.trans hT) N hG
  rw [average_eq_semicircle T (hA.trans hT) N] at hmass
  have h := hb N hN hG
  rw [hmass] at h
  unfold jensenFunctional
  have heq : ((∫ φ in (0 : ℝ)..π,
      Real.log ‖poweredZeta T N ((1.32 : ℂ) * Complex.exp (φ * I))‖) / π -
        Real.log ‖poweredZeta T N 0‖) / (2 * Real.log (4 * 1.32 / 3) * N) +
      1 / 2 + 4 / (π * T) + |gammaRemainder T| / π =
      (∫ φ in (0 : ℝ)..π,
        Real.log ‖poweredZeta T N ((1.32 : ℂ) * Complex.exp (φ * I))‖) /
          (2 * π * Real.log (4 * 1.32 / 3) * N) +
        1 / 2 + 4 / (π * T) - Real.log ‖poweredZeta T N 0‖ /
          (2 * Real.log (4 * 1.32 / 3) * N) + |gammaRemainder T| / π := by ring
  rwa [heq] at h

end LeanLab.RamareSaouter2003.Decomp419b

#print axioms LeanLab.RamareSaouter2003.Decomp419b.powered_analytic
#print axioms LeanLab.RamareSaouter2003.Decomp419b.zeroMass_eq_average
#print axioms LeanLab.RamareSaouter2003.Decomp419b.powered_conj
#print axioms LeanLab.RamareSaouter2003.Decomp419b.average_eq_semicircle
#print axioms LeanLab.RamareSaouter2003.Decomp419b.backlund_zero_mass_count
#print axioms LeanLab.RamareSaouter2003.Decomp419b.powered_jensen_count

#print axioms LeanLab.RamareSaouter2003.Decomp419b.paired_log_weight
