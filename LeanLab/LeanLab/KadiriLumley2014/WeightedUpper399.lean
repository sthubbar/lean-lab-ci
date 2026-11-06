/-
Source 4, arXiv 1310.6374v1 page 10 display 2.29.
An auxiliary elementary upper bound for the ordinary weighted integral.
This does not replace a sealed zero-sum assertion or certify a prime interval.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.WeightedAudit399

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory

/-- The reciprocal logarithm lies above its tangent at the positive lower logarithm. -/
theorem reciprocal_tangent {L l : ℝ} (hL : 0 < L) (hl : 0 < l) :
    1 / L - (l - L) / L ^ 2 ≤ 1 / l := by
  apply (le_div_iff₀ hl).mpr
  field_simp
  nlinarith [sq_nonneg (l - L)]

/-- The increasing zero-free weight is at most its lower value times a power envelope. -/
theorem weight_ratio_tangent {X R H y : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hH : 1 < H) (hy : H ≤ y) :
    X ^ (-1 / (R * Real.log y)) ≤ X ^ (-1 / (R * Real.log H)) *
      (y / H) ^ (Real.log X / (R * (Real.log H) ^ 2)) := by
  have hX0 : 0 < X := by linarith
  have hH0 : 0 < H := by linarith
  have hy0 : 0 < y := hH0.trans_le hy
  have hL : 0 < Real.log H := Real.log_pos hH
  have hl : 0 < Real.log y := Real.log_pos (hH.trans_le hy)
  have hA : 0 ≤ Real.log X := Real.log_nonneg hX
  rw [Real.rpow_def_of_pos hX0, Real.rpow_def_of_pos hX0,
    Real.rpow_def_of_pos (div_pos hy0 hH0), ← Real.exp_add,
    Real.log_div hy0.ne' hH0.ne']
  apply Real.exp_le_exp.mpr
  have ht := mul_le_mul_of_nonneg_left (reciprocal_tangent hL hl)
    (div_nonneg hA hR.le)
  field_simp at ht ⊢
  nlinarith

/-- The ordinary weighted kernel is dominated by an integrable power when its logarithmic domain holds. -/
theorem kernel_tangent_bound (m : ℕ) {X R H y : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hH : 1 < H) (hy : H ≤ y) :
    weightedKernel m X R y ≤
      (X ^ (-1 / (R * Real.log H)) / H ^ (Real.log X / (R * (Real.log H) ^ 2))) *
        y ^ (Real.log X / (R * (Real.log H) ^ 2) - (m : ℝ) - 1) := by
  have hH0 : 0 < H := by linarith
  have hy0 : 0 < y := hH0.trans_le hy
  have hb := div_le_div_of_nonneg_right (weight_ratio_tangent hX hR hH hy)
    (pow_nonneg hy0.le (m + 1))
  unfold weightedKernel
  apply hb.trans_eq
  rw [Real.div_rpow hy0.le hH0.le]
  rw [show Real.log X / (R * (Real.log H) ^ 2) - (m : ℝ) - 1 =
      Real.log X / (R * (Real.log H) ^ 2) - ((m + 1 : ℕ) : ℝ) from by push_cast; ring,
    Real.rpow_sub hy0, Real.rpow_natCast]
  ring

/-- A tangent-line power majorant bounds the ordinary weighted tail integral.
The denominator is positive by the displayed logarithmic domain. -/
theorem weightedIntegral_tangent_upper {m : ℕ} (hm : 0 < m) {X R H : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hH : 1 < H)
    (hlog : Real.log X < (m : ℝ) * R * (Real.log H) ^ 2) :
    (∫ y in Ioi H, weightedKernel m X R y) ≤
      X ^ (-1 / (R * Real.log H)) /
        (H ^ m * ((m : ℝ) - Real.log X / (R * (Real.log H) ^ 2))) := by
  have hH0 : 0 < H := by linarith
  have hL : 0 < Real.log H := Real.log_pos hH
  let α := Real.log X / (R * (Real.log H) ^ 2)
  have hα : α < (m : ℝ) := by
    dsimp [α]
    rw [div_lt_iff₀ (by positivity : 0 < R * (Real.log H) ^ 2)]
    nlinarith [hlog]
  have hp : α - (m : ℝ) - 1 < -1 := by linarith
  let C := X ^ (-1 / (R * Real.log H)) / H ^ α
  have hpower := (integrableOn_Ioi_rpow_of_lt hp hH0).const_mul C
  have hle : (∫ y in Ioi H, weightedKernel m X R y) ≤ ∫ y in Ioi H, C * y ^ (α - (m : ℝ) - 1) := by
    apply integral_mono_ae (weightedKernel_integrable hm hX hR hH) hpower
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact kernel_tangent_bound m hX hR hH hy.le
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hp hH0] at hle
  apply hle.trans_eq
  rw [show α - (m : ℝ) - 1 + 1 = α - (m : ℝ) from by ring,
    Real.rpow_sub hH0, Real.rpow_natCast]
  dsimp [C, α]
  field_simp
  convert (inv_neg (a := Real.log X - R * (Real.log H) ^ 2 * (m : ℝ))).symm using 1 <;> ring

/-- The elementary tangent argument gives twice the printed ordinary-integral expression.
This is an auxiliary upper bound and does not replace any sealed statement. -/
theorem weightedIntegral_le_twice_printed {m : ℕ} (hm : 0 < m) {X R H : ℝ}
    (hX : 1 < X) (hR : 0 < R) (hH : 1 < H)
    (hlog : Real.log X < (m : ℝ) * R * (Real.log H) ^ 2) :
    (∫ y in Ioi H, weightedKernel m X R y) ≤ 2 * printedIntegralBound m X R H := by
  have hH0 : 0 < H := by linarith
  have hL : 0 < Real.log H := Real.log_pos hH
  have hA : 0 < Real.log X := Real.log_pos hX
  apply (weightedIntegral_tangent_upper hm hX.le hR hH hlog).trans_eq
  unfold printedIntegralBound
  field_simp

end LeanLab.KadiriLumley2014.Task399
