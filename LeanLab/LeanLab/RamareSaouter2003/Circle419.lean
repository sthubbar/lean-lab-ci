import LeanLab.RamareSaouter2003.PowerReturns359

/-!
Rosser 1941 p. 224, the circle estimate for powers of zeta.
Backlund pp. 361 to 374 supplies the strip bounds and gamma remainder.
The Euler product comparison generalizes the existing PNTPort
ZetaFixedLowerBound proof from real part three halves to every real part above one.
That proof was ported from PrimeNumberTheoremAnd under Apache License 2.0.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Circle419
open Real Complex MeasureTheory Set

/-- LEAF. Rosser p. 224, Euler product lower bound before taking powers.
This retains the exact ratio instead of rounding it to a decimal. -/
theorem center_euler_lower (σ T : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta ((2 * σ : ℝ) : ℂ) / riemannZeta (σ : ℂ)‖ ≤
      ‖riemannZeta ((σ : ℂ) + T * I)‖ := by
  have mp : ∀ {s : ℂ}, 1 < s.re → Multipliable fun p : Nat.Primes =>
      (1 - (p : ℂ) ^ (-s))⁻¹ := fun hs => ⟨_, riemannZeta_eulerProduct_hasProd hs⟩
  have h₁ : 1 < (σ : ℂ).re := by simpa using hσ
  have h₂ : 1 < ((2 * σ : ℝ) : ℂ).re := by simp; linarith
  have h₃ : 1 < ((σ : ℂ) + T * I).re := by simpa using hσ
  suffices h : ‖riemannZeta ((2 * σ : ℝ) : ℂ) / riemannZeta (σ : ℂ)‖₊ ≤
      ‖riemannZeta ((σ : ℂ) + T * I)‖₊ by exact_mod_cast h
  rw [nnnorm_div, div_le_iff₀ (nnnorm_pos.mpr (riemannZeta_ne_zero_of_one_lt_re h₁)),
    ← riemannZeta_eulerProduct_tprod h₁, ← riemannZeta_eulerProduct_tprod h₂,
    ← riemannZeta_eulerProduct_tprod h₃, (mp h₁).nnnorm_tprod, (mp h₂).nnnorm_tprod,
    (mp h₃).nnnorm_tprod, ← (mp h₃).nnnorm.tprod_mul (mp h₁).nnnorm]
  refine (mp h₂).nnnorm.tprod_le_tprod (fun p => ?_) ((mp h₃).nnnorm.mul (mp h₁).nnnorm)
  simp only [nnnorm_inv, ← mul_inv]
  have hfact : ‖1 - (p : ℂ) ^ (-((2 * σ : ℝ) : ℂ))‖₊ =
      ‖1 + (p : ℂ) ^ (-(σ : ℂ))‖₊ * ‖1 - (p : ℂ) ^ (-(σ : ℂ))‖₊ := by
    rw [← nnnorm_mul]
    congr 1
    have hh : (p : ℂ) ^ (-((2 * σ : ℝ) : ℂ)) = ((p : ℂ) ^ (-(σ : ℂ))) ^ 2 := by
      convert Complex.cpow_nat_mul (p : ℂ) 2 (-(σ : ℂ)) using 2 <;> push_cast <;> ring
    calc
      _ = 1 - ((p : ℂ) ^ (-(σ : ℂ))) ^ 2 := congrArg (fun w : ℂ => 1 - w) hh
      _ = _ := by ring
  have hne : ∀ {s : ℂ}, 1 < s.re → (1 - (p : ℂ) ^ (-s)) ≠ 0 :=
    fun hs => Complex.one_sub_prime_cpow_ne_zero p.2 hs
  rw [inv_le_inv₀, hfact]
  · apply _root_.mul_le_mul_left
    rw [← norm_toNNReal, ← norm_toNNReal]
    apply Real.toNNReal_le_toNNReal
    calc
      ‖1 - (p : ℂ) ^ (-((σ : ℂ) + T * I))‖ ≤
          1 + ‖(p : ℂ) ^ (-((σ : ℂ) + T * I))‖ := by
        simpa using norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-((σ : ℂ) + T * I)))
      _ = ‖1 + (p : ℂ) ^ (-(σ : ℂ))‖ := by
        have hpos : 0 ≤ 1 + (p : ℝ) ^ (-σ) := by positivity
        rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
        simp only [neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_self, add_zero]
        rw [← Real.norm_of_nonneg hpos, ← Complex.norm_real, Complex.ofReal_add,
          Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ))]
        simp
  · exact norm_pos_iff.mpr (hne h₂)
  · exact mul_pos (norm_pos_iff.mpr (hne h₃)) (norm_pos_iff.mpr (hne h₁))

/-- LEAF. Rosser p. 224, passing from two zeta bounds to their averaged powers.
The nonnegative logarithmic envelope also covers a zero of the average. -/
theorem log_average_pow_le (a b : ℂ) (N : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (ha : ‖a‖ ≤ Real.exp E) (hb : ‖b‖ ≤ Real.exp E) :
    Real.log ‖(a ^ N + b ^ N) / 2‖ ≤ (N : ℝ) * E := by
  have hn : ‖(a ^ N + b ^ N) / 2‖ ≤ Real.exp ((N : ℝ) * E) := by
    rw [norm_div, Complex.norm_ofNat]
    have h := norm_add_le (a ^ N) (b ^ N)
    rw [norm_pow, norm_pow] at h
    have hpa := pow_le_pow_left₀ (norm_nonneg a) ha N
    have hpb := pow_le_pow_left₀ (norm_nonneg b) hb N
    rw [← Real.exp_nat_mul] at hpa hpb
    linarith
  by_cases hz : (a ^ N + b ^ N) / 2 = 0
  · simp only [hz, norm_zero, Real.log_zero]
    positivity
  · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hz)).mpr hn

/-- Backlund pp. 363 and 369, displays 56 and 77, used by Rosser p. 224.
The height T plus the radius bounds both ordinates separately.
The max in the first branch only makes its continuous extension total. -/
noncomputable def logEnvelope (T φ : ℝ) : ℝ :=
  let σ := 5 / 4 + 1.32 * Real.cos φ
  if 5 / 4 ≤ σ then
    Real.log (max 1 ‖riemannZeta ((max (5 / 4) σ : ℝ) : ℂ)‖)
  else if 1 ≤ σ then Real.log (Real.log (T + 1.32))
  else if 0 ≤ σ then
    Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) +
      (1 - σ) / 2 * Real.log ((T + 1.32) / (2 * π)) + Real.log (Real.log (T + 1.32))
  else (1 / 2 - σ) * Real.log ((T + 1.32) / (2 * π)) + Real.log (Real.log (T + 1.32))

/-- LEAF. Backlund pp. 363 and 369, displays 56 and 77, positivity on the circle.
This checks the total real envelope, not the analytic zeta estimate. -/
theorem logEnvelope_nonneg (T φ : ℝ) (hT : 1400 ≤ T) : 0 ≤ logEnvelope T φ := by
  have ht : 1 ≤ Real.log (T + 1.32) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1000) (by linarith : (1000 : ℝ) ≤ T + 1.32)
    linarith [VerifyU1333.log_thousand_ge]
  have hl := Real.log_nonneg ht
  have hb : 0 ≤ Real.log ((T + 1.32) / (2 * π)) := by
    apply Real.log_nonneg
    apply (one_le_div (by positivity : 0 < 2 * π)).mpr
    linarith [Real.pi_lt_four]
  have hc : 0 ≤ Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) := by
    apply Real.log_nonneg
    have hd : 0 < (T - 1.32) ^ 2 - 4 := by nlinarith
    exact (one_le_div hd).mpr (by linarith)
  unfold logEnvelope
  dsimp only
  split_ifs with h₁ h₂ h₃
  · exact Real.log_nonneg (le_max_left _ _)
  · exact hl
  · have he : 0 ≤ (1 - (5 / 4 + 1.32 * Real.cos φ)) / 2 := by linarith
    exact add_nonneg (add_nonneg hc (mul_nonneg he hb)) hl
  · have he : 0 ≤ 1 / 2 - (5 / 4 + 1.32 * Real.cos φ) := by linarith
    exact add_nonneg (mul_nonneg he hb) hl

/-- LEAF. Backlund pp. 371 and 372, integration of the piecewise circle envelope.
All four branches have continuous extensions to the whole angle interval. -/
theorem logEnvelope_integrable (T : ℝ) :
    IntervalIntegrable (logEnvelope T) volume 0 π := by
  classical
  have hc : Continuous (fun φ : ℝ => 5 / 4 + 1.32 * Real.cos φ) := by fun_prop
  have hz : Continuous (fun φ : ℝ =>
      riemannZeta ((max (5 / 4) (5 / 4 + 1.32 * Real.cos φ) : ℝ) : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro φ
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp
    · exact (Complex.continuous_ofReal.comp (continuous_const.max hc)).continuousAt
    · intro h
      have he := congrArg Complex.re h
      have hh := le_max_left (5 / 4 : ℝ) (5 / 4 + 1.32 * Real.cos φ)
      simp only [Complex.ofReal_re, Complex.one_re] at he
      linarith
  have hfirst : Continuous (fun φ : ℝ =>
      Real.log (max 1 ‖riemannZeta ((max (5 / 4) (5 / 4 + 1.32 * Real.cos φ) : ℝ) : ℂ)‖)) :=
    (continuous_const.max hz.norm).log (fun φ => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
  have hite {p : ℝ → Prop} {f g : ℝ → ℝ}
      (hp : MeasurableSet {φ | p φ})
      (hf : IntervalIntegrable f volume 0 π) (hg : IntervalIntegrable g volume 0 π) :
      IntervalIntegrable (fun φ => if p φ then f φ else g φ) volume 0 π := by
    apply intervalIntegrable_iff.mpr
    exact Integrable.piecewise hp.nullMeasurableSet hf.def'.integrableOn hg.def'.integrableOn
  unfold logEnvelope
  apply hite (isClosed_le continuous_const hc).measurableSet (hfirst.intervalIntegrable 0 π)
  apply hite (isClosed_le continuous_const hc).measurableSet intervalIntegrable_const
  apply hite (isClosed_le continuous_const hc).measurableSet
  · exact (by fun_prop : Continuous (fun φ : ℝ =>
        Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) +
          (1 - (5 / 4 + 1.32 * Real.cos φ)) / 2 * Real.log ((T + 1.32) / (2 * π)) +
            Real.log (Real.log (T + 1.32)))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun φ : ℝ =>
        (1 / 2 - (5 / 4 + 1.32 * Real.cos φ)) * Real.log ((T + 1.32) / (2 * π)) +
          Real.log (Real.log (T + 1.32)))).intervalIntegrable _ _

/-- LEAF. Rosser pp. 223 and 224, integrability of the powered Jensen integrand.
The pole of each shifted zeta function lies outside the circle. -/
theorem powered_log_integrable (T : ℝ) (hT : 1400 ≤ T) (N : ℕ) :
    IntervalIntegrable (fun φ : ℝ =>
      Real.log ‖Decomp359g.poweredZeta T N ((1.32 : ℂ) * Complex.exp (φ * I))‖) volume 0 π := by
  have hanalytic : AnalyticOnNhd ℂ (Decomp359g.poweredZeta T N)
      (Metric.sphere 0 |(1.32 : ℝ)|) := by
    intro z hz
    have hn : ‖z‖ = (1.32 : ℝ) := by simpa only [Metric.mem_sphere, dist_zero_right, abs_of_pos (by norm_num : (0 : ℝ) < 1.32)] using hz
    have hplus : z + 5 / 4 + T * I ≠ 1 := by
      intro hh
      have he := congrArg Complex.im hh
      have hab := Complex.abs_im_le_norm z
      simp only [Complex.add_im, Complex.div_ofNat_im, Complex.im_ofNat, zero_div,
        add_zero, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, zero_add, Complex.one_im] at he
      have hm : |z.im| = T := by rw [show z.im = -T by linarith, abs_neg, abs_of_nonneg (by linarith)]
      rw [hm, hn] at hab
      linarith
    have hminus : z + 5 / 4 - T * I ≠ 1 := by
      intro hh
      have he := congrArg Complex.im hh
      have hab := Complex.abs_im_le_norm z
      simp only [Complex.sub_im, Complex.add_im, Complex.div_ofNat_im, Complex.im_ofNat,
        zero_div, add_zero, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, zero_add, Complex.one_im] at he
      have hm : |z.im| = T := by rw [show z.im = T by linarith, abs_of_nonneg (by linarith)]
      rw [hm, hn] at hab
      linarith
    have hp : AnalyticAt ℂ (fun w : ℂ => riemannZeta (w + 5 / 4 + T * I)) z := by
      exact (analyticOn_riemannZeta _ hplus).comp (f := fun w : ℂ => w + 5 / 4 + T * I) (x := z)
        ((analyticAt_id.add analyticAt_const).add analyticAt_const)
    have hm : AnalyticAt ℂ (fun w : ℂ => riemannZeta (w + 5 / 4 - T * I)) z := by
      exact (analyticOn_riemannZeta _ hminus).comp (f := fun w : ℂ => w + 5 / 4 - T * I) (x := z)
        ((analyticAt_id.add analyticAt_const).sub analyticAt_const)
    exact (hp.pow N |>.add (hm.pow N)).div_const
  have hfull := hanalytic.meromorphicOn.circleIntegrable_log_norm
  have hhalf := hfull.mono_set (show Set.uIcc (0 : ℝ) π ⊆ Set.uIcc 0 (2 * π) by
    simp only [Set.uIcc_of_le Real.pi_pos.le, Set.uIcc_of_le (show (0 : ℝ) ≤ 2 * π by positivity)]
    exact Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))
  simpa only [circleMap, zero_add, add_zero, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_ofScientific] using hhalf

end LeanLab.RamareSaouter2003.Circle419

#print axioms LeanLab.RamareSaouter2003.Circle419.center_euler_lower
#print axioms LeanLab.RamareSaouter2003.Circle419.log_average_pow_le
#print axioms LeanLab.RamareSaouter2003.Circle419.logEnvelope_nonneg
#print axioms LeanLab.RamareSaouter2003.Circle419.logEnvelope_integrable
#print axioms LeanLab.RamareSaouter2003.Circle419.powered_log_integrable
