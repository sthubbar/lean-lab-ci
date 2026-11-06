import LeanLab.ChenDoubleSieve.Decomp350a

/-!
An exact reduction of the remaining logarithmic quadrature.
Source: https://arxiv.org/pdf/0705.1652, page 41 equation 10.12 and page 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Task350
open Task275

/-- Integration by parts removes a triangular reciprocal squared integral.
Source: page 41 equation 10.12, derived exact integration helper. -/
theorem reciprocal_triangle {H : ℝ → ℝ} {a k : ℝ} (ha : 0 < a) (hak : a ≤ k)
    (hH : ContinuousOn H (Icc a k)) :
    (∫ t in a..k, (∫ s in t..k, H s) / t ^ 2) =
      (∫ s in a..k, H s) / a - ∫ t in a..k, H t / t := by
  have hk := ha.trans_le hak
  have hHu : ContinuousOn H (uIcc a k) := by rwa [uIcc_of_le hak]
  have hP : ContinuousOn (fun t => ∫ s in t..k, H s) (uIcc a k) :=
    continuousOn_primitive_interval_left hHu.integrableOn_uIcc
  have hv : ContinuousOn (fun t : ℝ => -(1 / t)) (uIcc a k) := by
    rw [uIcc_of_le hak]
    exact (continuousOn_const.div continuousOn_id (fun t ht => (ha.trans_le ht.1).ne')).neg
  have hu' : IntervalIntegrable (fun t => -H t) volume a k := hHu.intervalIntegrable.neg
  have hv' : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume a k := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hak]
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero _ (ha.trans_le ht.1).ne')
  have hPd : ∀ t ∈ Ioo (min a k) (max a k),
      HasDerivAt (fun t => ∫ s in t..k, H s) (-H t) t := by
    rw [min_eq_left hak, max_eq_right hak]
    intro t ht
    have hi : IntervalIntegrable H volume t k := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.2.le]
      exact hH.mono (fun s hs => ⟨ht.1.le.trans hs.1, hs.2⟩)
    exact integral_hasDerivAt_left hi
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hH.mono Ioo_subset_Icc_self) t ht)
      (hH.continuousAt (Icc_mem_nhds ht.1 ht.2))
  have hvd : ∀ t ∈ Ioo (min a k) (max a k),
      HasDerivAt (fun t : ℝ => -(1 / t)) (1 / t ^ 2) t := by
    rw [min_eq_left hak, max_eq_right hak]
    intro t ht
    have ht0 : t ≠ 0 := (ha.trans ht.1).ne'
    convert ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht0).neg using 1
    · funext x
      rfl
    · dsimp only [id_eq]
      ring
  have he := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hP hv hPd hvd hu' hv'
  have hm : (∫ t in a..k, (∫ s in t..k, H s) * (1 / t ^ 2)) =
      ∫ t in a..k, (∫ s in t..k, H s) / t ^ 2 := by
    apply integral_congr
    intro t _
    simp only [mul_one_div]
  have hn : (∫ t in a..k, -H t * -(1 / t)) = ∫ t in a..k, H t / t := by
    apply integral_congr
    intro t _
    ring
  rw [hm, hn] at he
  simpa [div_eq_mul_inv] using he

/-- The triangular logarithmic integral after removing its middle coordinate.
Source: page 41 equation 10.12, derived two dimensional integral. -/
def twofoldMajorant (c : ℝ) (lower last : ℝ → ℝ) (a b : ℝ) (weight : ℝ → ℝ) : ℝ :=
  ∫ t1 in a..b,
    (∫ t3 in t1..kappa2,
      c * log (last t3 / lower t3) / t3 * (1 / t1 - 1 / t3)) / weight t1

/-- The threefold majorant equals the twofold majorant exactly.
Source: page 41 equation 10.12, derived integration by parts. -/
theorem logMajorant_eq_twofold {c a b : ℝ} {lower last : ℝ → ℝ}
    (hab : a ≤ b) (ha : kappa1 ≤ a) (hb : b ≤ kappa2)
    (hl : ContinuousOn lower (Icc kappa1 kappa2))
    (hr : ContinuousOn last (Icc kappa1 kappa2))
    (hlpos : ∀ t ∈ Icc kappa1 kappa2, 0 < lower t)
    (hrpos : ∀ t ∈ Icc kappa1 kappa2, 0 < last t) (weight : ℝ → ℝ) :
    logMajorant c lower last a b weight = twofoldMajorant c lower last a b weight := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hH : ContinuousOn (fun t => c * log (last t / lower t) / t) (Icc kappa1 kappa2) := by
    apply ContinuousOn.div _ continuousOn_id (fun t ht => (hk.trans_le ht.1).ne')
    apply continuousOn_const.mul
    exact (hr.div hl (fun t ht => (hlpos t ht).ne')).log
      (fun t ht => (div_pos (hrpos t ht) (hlpos t ht)).ne')
  unfold logMajorant twofoldMajorant
  apply integral_congr
  intro t ht
  dsimp only
  rw [uIcc_of_le hab] at ht
  have ht0 := hk.trans_le (ha.trans ht.1)
  have htk := ht.2.trans hb
  have hH' : ContinuousOn (fun t => c * log (last t / lower t) / t) (Icc t kappa2) :=
    hH.mono (fun s hs => ⟨(ha.trans ht.1).trans hs.1, hs.2⟩)
  congr 1
  rw [reciprocal_triangle ht0 htk hH']
  have hi : IntervalIntegrable (fun s => c * log (last s / lower s) / s) volume t kappa2 :=
    (by rwa [uIcc_of_le htk] : ContinuousOn _ (uIcc t kappa2)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s => (c * log (last s / lower s) / s) / s) volume t kappa2 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le htk]
    exact hH'.div continuousOn_id (fun s hs => (ht0.trans_le hs.1).ne')
  rw [← intervalIntegral.integral_div, ← integral_sub (hi.div_const t) hi2]
  apply integral_congr
  intro s _
  dsimp only
  ring

end LeanLab.ChenDoubleSieve.Task350
