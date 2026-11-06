/-
Source 4, arXiv 1310.6374v1 page 10 display 2.29.
Auxiliary diagnostic for its ordinary real integral J_m.
This does not refute the actual zero sum or any prime interval theorem.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory

/-- The ordinary integral kernel phi_m on cited pages 9 and 10. -/
noncomputable def weightedKernel (m : ℕ) (X R y : ℝ) : ℝ :=
  X ^ (-1 / (R * Real.log y)) / y ^ (m + 1)

/-- The printed upper expression for J_m in cited display 2.29.
Positive powers and X rpow replace their equivalent exponential spelling. -/
noncomputable def printedIntegralBound (m : ℕ) (X R H : ℝ) : ℝ :=
  R / (2 * Real.log X) * (Real.log H) ^ 2 /
    (((m : ℝ) * R / Real.log X) * (Real.log H) ^ 2 - 1) /
      H ^ m * X ^ (-1 / (R * Real.log H))

/-- The weighted kernel lies between its lower-end weight times the reciprocal power and that reciprocal power. -/
theorem weightedKernel_bounds (m : ℕ) {X R H y : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hH : 1 < H) (hy : H ≤ y) :
    0 ≤ weightedKernel m X R y ∧
      weightedKernel m X R y ≤ 1 / y ^ (m + 1) ∧
      X ^ (-1 / (R * Real.log H)) / y ^ (m + 1) ≤ weightedKernel m X R y := by
  have hlogH : 0 < Real.log H := Real.log_pos hH
  have hlog : Real.log H ≤ Real.log y := Real.log_le_log (by linarith) hy
  have hy0 : 0 < y := by linarith
  have hrec : 1 / (R * Real.log y) ≤ 1 / (R * Real.log H) :=
    one_div_le_one_div_of_le (mul_pos hR hlogH)
      (mul_le_mul_of_nonneg_left hlog hR.le)
  have hw1 : X ^ (-1 / (R * Real.log y)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX
      (div_nonpos_of_nonpos_of_nonneg (by norm_num)
        (mul_nonneg hR.le (hlogH.trans_le hlog).le))
  have hwH : X ^ (-1 / (R * Real.log H)) ≤ X ^ (-1 / (R * Real.log y)) :=
    Real.rpow_le_rpow_of_exponent_le hX (by simpa only [neg_div] using neg_le_neg hrec)
  unfold weightedKernel
  exact ⟨by positivity, div_le_div_of_nonneg_right hw1 (by positivity),
    div_le_div_of_nonneg_right hwH (by positivity)⟩

/-- The unweighted reciprocal power has the exact ordinary tail integral. -/
theorem integral_reciprocal_power {m : ℕ} (hm : 0 < m) {H : ℝ} (hH : 0 < H) :
    (∫ y in Ioi H, 1 / y ^ (m + 1)) = 1 / ((m : ℝ) * H ^ m) := by
  have hfun : (∫ y in Ioi H, 1 / y ^ (m + 1)) =
      ∫ y in Ioi H, y ^ (-((m : ℝ) + 1)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) from by simp,
      Real.rpow_neg (hH.trans hy).le, Real.rpow_natCast]
    simp
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  rw [hfun, integral_Ioi_rpow_of_lt (by linarith : -((m : ℝ) + 1) < -1) hH]
  rw [show -((m : ℝ) + 1) + 1 = -(m : ℝ) from by ring,
    Real.rpow_neg hH.le, Real.rpow_natCast]
  field_simp

/-- The reciprocal-power kernel is integrable on every positive tail. -/
theorem reciprocal_power_integrable {m : ℕ} (hm : 0 < m) {H : ℝ} (hH : 0 < H) :
    IntegrableOn (fun y : ℝ => 1 / y ^ (m + 1)) (Ioi H) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have h := integrableOn_Ioi_rpow_of_lt (a := -((m : ℝ) + 1)) (by linarith) hH
  apply h.congr_fun _ measurableSet_Ioi
  intro y hy
  dsimp only
  rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) from by simp,
    Real.rpow_neg (hH.trans hy).le, Real.rpow_natCast]
  simp

/-- The weighted kernel is integrable because its weight is between zero and one. -/
theorem weightedKernel_integrable {m : ℕ} (hm : 0 < m) {X R H : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hH : 1 < H) :
    IntegrableOn (weightedKernel m X R) (Ioi H) := by
  have hc : ContinuousOn (weightedKernel m X R) (Ioi H) := by
    unfold weightedKernel
    fun_prop (disch := first | positivity |
      (intro y hy; have hylog := Real.log_pos (hH.trans hy); positivity [hH.trans hy]))
  apply (reciprocal_power_integrable hm (by linarith : 0 < H)).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (weightedKernel_bounds m hX hR hH hy.le).1]
  exact (weightedKernel_bounds m hX hR hH hy.le).2.1

/-- The ordinary J_m integral is at least its lower-end weight times the exact reciprocal-power integral. -/
theorem weightedIntegral_lower {m : ℕ} (hm : 0 < m) {X R H : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hH : 1 < H) :
    X ^ (-1 / (R * Real.log H)) / ((m : ℝ) * H ^ m) ≤
      ∫ y in Ioi H, weightedKernel m X R y := by
  have hi := reciprocal_power_integrable hm (by linarith : 0 < H)
  have hc := hi.const_mul (X ^ (-1 / (R * Real.log H)))
  have h := integral_mono_ae hc (weightedKernel_integrable hm hX hR hH) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simpa only [mul_one_div] using (weightedKernel_bounds m hX hR hH hy.le).2.2)
  rw [integral_const_mul, integral_reciprocal_power hm (by linarith : 0 < H)] at h
  simpa only [mul_one_div] using h

/-- At a concrete valid domain point the printed ordinary-integral bound is strictly too small.
This diagnostic concerns source display 2.29 and leaves the actual zero-sum statement open. -/
theorem weightedIntegral_exceeds_printed :
    printedIntegralBound 2 (Real.exp 4) 1 (Real.exp 3) <
      ∫ y in Ioi (Real.exp 3), weightedKernel 2 (Real.exp 4) 1 y := by
  have hl := weightedIntegral_lower (m := 2) (by norm_num)
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 4)) (by norm_num : (0 : ℝ) < 1)
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 3))
  apply lt_of_lt_of_le _ hl
  unfold printedIntegralBound
  simp only [Real.log_exp, Nat.cast_ofNat]
  have he : 0 < Real.exp 3 := Real.exp_pos 3
  have hw : 0 < (Real.exp 4) ^ (-1 / ((1 : ℝ) * 3)) := Real.rpow_pos_of_pos (Real.exp_pos 4) _
  norm_num
  field_simp
  nlinarith

/-- Throughout the smaller logarithmic domain, the printed ordinary-integral expression
is below the elementary lower bound. This is a source diagnostic only. -/
theorem printedIntegralBound_lt_lower {m : ℕ} (hm : 0 < m) {X R H : ℝ}
    (hX : 1 < X) (hR : 0 < R) (hH : 1 < H)
    (hhalf : 2 * Real.log X < (m : ℝ) * R * (Real.log H) ^ 2) :
    printedIntegralBound m X R H <
      X ^ (-1 / (R * Real.log H)) / ((m : ℝ) * H ^ m) := by
  have hH0 : 0 < H := by linarith
  have hL : 0 < Real.log H := Real.log_pos hH
  have hA : 0 < Real.log X := Real.log_pos hX
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  let α := Real.log X / (R * (Real.log H) ^ 2)
  have hαm : 2 * α < (m : ℝ) := by
    dsimp [α]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < R * (Real.log H) ^ 2)]
    nlinarith [hhalf]
  have hma : 0 < (m : ℝ) - α := by linarith
  have heq : printedIntegralBound m X R H =
      X ^ (-1 / (R * Real.log H)) / (2 * H ^ m * ((m : ℝ) - α)) := by
    unfold printedIntegralBound
    dsimp [α]
    field_simp
  rw [heq]
  apply div_lt_div_of_pos_left (Real.rpow_pos_of_pos (by linarith : 0 < X) _)
    (by positivity : (0 : ℝ) < (m : ℝ) * H ^ m)
  nlinarith [mul_pos (pow_pos hH0 m) (sub_pos.mpr hαm)]

/-- The ordinary-integral obstruction also occurs at the published H and R0,
with X = exp 38 and m = 2. It is not a statement about an actual zero sum. -/
theorem published_weightedIntegral_exceeds_printed :
    printedIntegralBound 2 (Real.exp 38) 5.69693 30610000000 <
      ∫ y in Ioi 30610000000, weightedKernel 2 (Real.exp 38) 5.69693 y := by
  have he : Real.exp (10 : ℝ) < (30610000000 : ℝ) := by
    have h3 : Real.exp 1 < (3 : ℝ) := by linarith [Real.exp_one_lt_three]
    have hpow := pow_le_pow_left₀ (Real.exp_pos 1).le h3.le 10
    have heq : Real.exp (10 : ℝ) = Real.exp 1 ^ 10 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [← heq] at hpow
    norm_num at hpow
    linarith
  have hlog : (10 : ℝ) < Real.log 30610000000 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 30610000000)).mpr he
  have hb := printedIntegralBound_lt_lower (m := 2) (by norm_num)
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 38))
    (by norm_num : (0 : ℝ) < 5.69693) (by norm_num : (1 : ℝ) < 30610000000)
    (by simp only [Real.log_exp, Nat.cast_ofNat]; nlinarith [sq_nonneg (Real.log 30610000000 - 10)])
  exact hb.trans_le (weightedIntegral_lower (m := 2) (by norm_num)
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 38))
    (by norm_num : (0 : ℝ) < 5.69693) (by norm_num : (1 : ℝ) < 30610000000))

end LeanLab.KadiriLumley2014.Task399
