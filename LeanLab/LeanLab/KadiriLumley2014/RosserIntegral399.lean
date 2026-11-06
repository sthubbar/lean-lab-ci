/-
P0059 page 7 displays 2.40 to 2.42.
Source 4, arXiv 1310.6374 page 9, integrals before displays 2.22 to 2.24.
Exact scalar integration steps for the three Rosser leaves.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.RosserScalar399
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory Filter Topology

/-- The reciprocal-power logarithmic primitive on cited page 9, with general positive scale c. -/
noncomputable def logPowerPrimitive (m : ℕ) (c t : ℝ) : ℝ :=
  (1 + (m : ℝ) * Real.log (t / c)) / ((m : ℝ) ^ 2 * t ^ m)

/-- A positive constant scale cancels from the derivative of the logarithmic ratio. -/
theorem log_ratio_derivative {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => Real.log (t / c)) (1 / t) t := by
  have h := ((hasDerivAt_id t).div_const c).log (div_ne_zero ht.ne' hc.ne')
  convert h using 1
  · ext x
    rfl
  · simp only [id_eq]
    field_simp

/-- Differentiating the positive-order logarithmic primitive gives minus log of t over c divided by t to m plus one. -/
theorem logPowerPrimitive_derivative {m : ℕ} (hm : 0 < m) {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (logPowerPrimitive m c) (-Real.log (t / c) / t ^ (m + 1)) t := by
  rcases m with _ | n
  · omega
  have hnum := ((log_ratio_derivative hc ht).const_mul ((n : ℝ) + 1)).const_add 1
  have hden := ((hasDerivAt_id t).pow (n + 1)).const_mul (((n : ℝ) + 1) ^ 2)
  have h := hnum.div hden (mul_ne_zero (by positivity) (pow_ne_zero _ ht.ne'))
  convert h using 1
  · ext x
    simp only [logPowerPrimitive, Nat.cast_add, Nat.cast_one, Pi.div_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.pow_apply, id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    simp only [pow_succ]
    field_simp
    ; ring

/-- The finite logarithmic reciprocal-power integral is the exact primitive difference used for S2. -/
theorem integral_log_power {m : ℕ} (hm : 0 < m) {c U V : ℝ}
    (hc : 0 < c) (hU : 0 < U) (hUV : U ≤ V) :
    (∫ t in U..V, Real.log (t / c) / t ^ (m + 1)) =
      logPowerPrimitive m c U - logPowerPrimitive m c V := by
  have hcont : ContinuousOn (fun t : ℝ => Real.log (t / c) / t ^ (m + 1)) (Icc U V) := by
    fun_prop (disch := intro t ht; positivity [hU.trans_le ht.1])
  have hi : IntervalIntegrable (fun t : ℝ => Real.log (t / c) / t ^ (m + 1)) volume U V :=
    hcont.intervalIntegrable_of_Icc hUV
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => -logPowerPrimitive m c t)
    (f' := fun t => Real.log (t / c) / t ^ (m + 1))
    (fun t ht => by
      rw [uIcc_of_le hUV] at ht
      convert (logPowerPrimitive_derivative hm hc (hU.trans_le ht.1)).neg using 1 ; ring) hi
  linarith

/-- The reciprocal logarithmic integral is the difference of squared logarithms,
the first integration identity on cited page 9. -/
theorem integral_log_reciprocal {c U V : ℝ}
    (hc : 0 < c) (hU : 0 < U) (hUV : U ≤ V) :
    (∫ t in U..V, Real.log (t / c) / t) =
      ((Real.log (V / c)) ^ 2 - (Real.log (U / c)) ^ 2) / 2 := by
  have hd : ∀ t ∈ Icc U V,
      HasDerivAt (fun t : ℝ => (Real.log (t / c)) ^ 2 / 2) (Real.log (t / c) / t) t := by
    intro t ht
    convert ((log_ratio_derivative hc (hU.trans_le ht.1)).pow 2).div_const 2 using 1 ; ring
  have hcont : ContinuousOn (fun t : ℝ => Real.log (t / c) / t) (Icc U V) := by
    fun_prop (disch := intro t ht; positivity [hU.trans_le ht.1])
  have hi : IntervalIntegrable (fun t : ℝ => Real.log (t / c) / t) volume U V :=
    hcont.intervalIntegrable_of_Icc hUV
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le hUV] using ht)) hi
  linarith

/-- The positive-order logarithmic primitive vanishes at infinity, so its upper endpoint disappears for S3. -/
theorem logPowerPrimitive_tendsto_zero {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (logPowerPrimitive m c) Filter.atTop (nhds 0) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog := (isLittleO_log_rpow_atTop hmr).tendsto_div_nhds_zero
  simp only [Real.rpow_natCast] at hlog
  have hpow : Tendsto (fun t : ℝ => t ^ m) atTop atTop :=
    tendsto_pow_atTop (show m ≠ 0 from by omega)
  have hone : Filter.Tendsto (fun t : ℝ => 1 / t ^ m) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hcst : Filter.Tendsto (fun t : ℝ => Real.log c / t ^ m) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hlim := (hone.add ((hlog.sub hcst).const_mul (m : ℝ))).div_const ((m : ℝ) ^ 2)
  simp only [sub_zero, mul_zero, add_zero, zero_div] at hlim
  apply hlim.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  dsimp only [logPowerPrimitive]
  rw [Real.log_div ht.ne' hc.ne']
  field_simp

/-- The infinite logarithmic reciprocal-power integral is the exact remaining primitive value for S3. -/
theorem integral_Ioi_log_power {m : ℕ} (hm : 0 < m) {c H : ℝ}
    (hc : 0 < c) (hH : 0 < H) (hcH : c ≤ H) :
    (∫ t in Ioi H, Real.log (t / c) / t ^ (m + 1)) = logPowerPrimitive m c H := by
  have hd : ∀ t ∈ Ici H, HasDerivAt (fun t => -logPowerPrimitive m c t)
      (Real.log (t / c) / t ^ (m + 1)) t := by
    intro t ht
    convert (logPowerPrimitive_derivative hm hc (hH.trans_le ht)).neg using 1 ; ring
  have hp : ∀ t ∈ Ioi H, 0 ≤ Real.log (t / c) / t ^ (m + 1) := by
    intro t ht
    have hratio : 1 ≤ t / c := (one_le_div hc).mpr (hcH.trans ht.le)
    exact div_nonneg (Real.log_nonneg hratio) (pow_nonneg (hH.trans ht).le _)
  have hlim : Filter.Tendsto (fun t => -logPowerPrimitive m c t) Filter.atTop (nhds 0) := by
    simpa only [neg_zero] using (logPowerPrimitive_tendsto_zero hm hc).neg
  simpa only [zero_sub, neg_neg] using integral_Ioi_of_hasDerivAt_of_nonneg' hd hp hlim

end LeanLab.KadiriLumley2014.Task399
