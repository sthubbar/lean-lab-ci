/-
P0059 page 7 display 2.43 and source 4, arXiv 1310.6374 page 9 display 2.25.
The primitive underlying the density reciprocal-power estimate.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroStep399

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory

/-- The positive-tail primitive from the integration by parts in cited display 2.25. -/
noncomputable def densityPrimitive (m : ℕ) (c1 c2 c3 t : ℝ) : ℝ :=
  (c1 * t + c2 * Real.log t + c3) / t ^ (m + 1) +
    c1 / ((m : ℝ) * t ^ m) + c2 / (((m : ℝ) + 1) * t ^ (m + 1))

/-- The primitive differentiates to the density envelope times minus the derivative power. -/
theorem densityPrimitive_derivative {m : ℕ} (hm : 0 < m)
    (c1 c2 c3 : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (densityPrimitive m c1 c2 c3)
      (-((m : ℝ) + 1) * (c1 * t + c2 * Real.log t + c3) / t ^ (m + 2)) t := by
  rcases m with _ | n
  · omega
  have hB : HasDerivAt (fun t : ℝ => c1 * t + c2 * Real.log t + c3)
      (c1 + c2 / t) t := by
    convert (((hasDerivAt_id t).const_mul c1).add
      ((Real.hasDerivAt_log ht.ne').const_mul c2)).add_const c3 using 1
    · ext x
      simp only [Pi.add_apply, id_eq]
    · ring
  have h1 := hB.div ((hasDerivAt_id t).pow (n + 2)) (pow_ne_zero _ ht.ne')
  have h2 := (hasDerivAt_const t c1).div
    (((hasDerivAt_id t).pow (n + 1)).const_mul ((n : ℝ) + 1))
    (mul_ne_zero (by positivity) (pow_ne_zero _ ht.ne'))
  have h3 := (hasDerivAt_const t c2).div
    (((hasDerivAt_id t).pow (n + 2)).const_mul ((n : ℝ) + 2))
    (mul_ne_zero (by positivity) (pow_ne_zero _ ht.ne'))
  convert (h1.add h2).add h3 using 1
  · ext x
    simp only [densityPrimitive, Pi.add_apply, Pi.div_apply, Pi.pow_apply, id_eq, Nat.cast_add, Nat.cast_one]
    congr 2; ring
  · simp only [Pi.pow_apply, id_eq,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.add_sub_cancel,
      show n + 2 - 1 = n + 1 from by omega]
    simp only [pow_succ]
    field_simp
    ring

/-- The finite integral of the density envelope times the reciprocal-power derivative is an endpoint difference. -/
theorem integral_density_power {m : ℕ} (hm : 0 < m) (c1 c2 c3 : ℝ)
    {H V : ℝ} (hH : 0 < H) (hHV : H ≤ V) :
    (∫ t in H..V, ((m : ℝ) + 1) * (c1 * t + c2 * Real.log t + c3) /
      t ^ (m + 2)) = densityPrimitive m c1 c2 c3 H - densityPrimitive m c1 c2 c3 V := by
  have hc : ContinuousOn (fun t : ℝ => ((m : ℝ) + 1) *
      (c1 * t + c2 * Real.log t + c3) / t ^ (m + 2)) (Icc H V) := by
    fun_prop (disch := intro t ht; positivity [hH.trans_le ht.1])
  have hi : IntervalIntegrable (fun t : ℝ => ((m : ℝ) + 1) *
      (c1 * t + c2 * Real.log t + c3) / t ^ (m + 2)) volume H V :=
    hc.intervalIntegrable_of_Icc hHV
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => -densityPrimitive m c1 c2 c3 t)
    (f' := fun t => ((m : ℝ) + 1) * (c1 * t + c2 * Real.log t + c3) / t ^ (m + 2))
    (fun t ht => by
      rw [uIcc_of_le hHV] at ht
      convert (densityPrimitive_derivative hm c1 c2 c3 (hH.trans_le ht.1)).neg using 1; ring) hi
  linarith

end LeanLab.KadiriLumley2014.Task399
