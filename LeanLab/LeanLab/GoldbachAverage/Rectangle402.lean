import LeanLab.GoldbachAverage.State402

/-!
Goldston and Suriajaya, arXiv 2110.14250v2 page 19 proof of Lemma 3.
The fixed psi application has bounded measurable squares on both compact rectangles.
This supplies the Fubini hypotheses independently of either comparison leaf.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Rectangle402
open MeasureTheory Set Filter

/-- Compact additive rectangle integrability in the P0051 page 19 proof of eq. 71. -/
theorem additive_square_integrable (A B U : ℝ) (hA : 0 ≤ A) (hU : 0 ≤ U) :
    Integrable (fun p : ℝ × ℝ =>
      (Chebyshev.psi (p.2 + p.1) - Chebyshev.psi p.2 - p.1) ^ 2)
      ((volume.restrict (Ioc 0 U)).prod (volume.restrict (Ioc A B))) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (Chebyshev.psi (p.2 + p.1) - Chebyshev.psi p.2 - p.1) ^ 2) :=
    (((Chebyshev.psi_mono.measurable.comp (measurable_snd.add measurable_fst)).sub
      (Chebyshev.psi_mono.measurable.comp measurable_snd)).sub measurable_fst).pow_const 2
  refine Integrable.of_bound hm.aestronglyMeasurable ((2 * Chebyshev.psi (B + U) + U) ^ 2) ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
  obtain ⟨hu, hy⟩ := hp
  have hψ1 := Chebyshev.psi_mono (show p.2 + p.1 ≤ B + U by linarith [hy.2, hu.2])
  have hψ2 := Chebyshev.psi_mono (show p.2 ≤ B + U by linarith [hy.2])
  have ha : |Chebyshev.psi (p.2 + p.1) - Chebyshev.psi p.2 - p.1| ≤
      2 * Chebyshev.psi (B + U) + U := by
    rw [abs_le]
    constructor <;> linarith [Chebyshev.psi_nonneg (p.2 + p.1),
      Chebyshev.psi_nonneg p.2, Chebyshev.psi_nonneg (B + U), hu.1, hu.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2

/-- Compact relative rectangle integrability in the P0051 page 19 change of variables. -/
theorem relative_square_integrable (A B D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    Integrable (fun p : ℝ × ℝ =>
      (Chebyshev.psi ((1 + p.1) * p.2) - Chebyshev.psi p.2 - p.1 * p.2) ^ 2)
      ((volume.restrict (Ioc 0 D)).prod (volume.restrict (Ioc A B))) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (Chebyshev.psi ((1 + p.1) * p.2) - Chebyshev.psi p.2 - p.1 * p.2) ^ 2) :=
    (((Chebyshev.psi_mono.measurable.comp ((measurable_const.add measurable_fst).mul measurable_snd)).sub
      (Chebyshev.psi_mono.measurable.comp measurable_snd)).sub (measurable_fst.mul measurable_snd)).pow_const 2
  refine Integrable.of_bound hm.aestronglyMeasurable ((2 * Chebyshev.psi ((1 + D) * B) + D * B) ^ 2) ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
  obtain ⟨hd, hy⟩ := hp
  have hy0 : 0 ≤ p.2 := by linarith [hy.1]
  have hdy : 0 ≤ p.1 * p.2 := mul_nonneg hd.1.le hy0
  have hdyB : p.1 * p.2 ≤ D * B := mul_le_mul hd.2 hy.2 hy0 hD
  have hu : (1 + p.1) * p.2 ≤ (1 + D) * B := by nlinarith [hy.2]
  have hyB : p.2 ≤ (1 + D) * B := by nlinarith [hy.2, mul_nonneg hD hB]
  have hψ1 := Chebyshev.psi_mono hu
  have hψ2 := Chebyshev.psi_mono hyB
  have ha : |Chebyshev.psi ((1 + p.1) * p.2) - Chebyshev.psi p.2 - p.1 * p.2| ≤
      2 * Chebyshev.psi ((1 + D) * B) + D * B := by
    rw [abs_le]
    constructor <;> linarith [Chebyshev.psi_nonneg ((1 + p.1) * p.2),
      Chebyshev.psi_nonneg p.2, Chebyshev.psi_nonneg ((1 + D) * B)]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2

/-- The multiplicative rectangle comparison in the P0051 page 19 proof of Lemma 3.
Scale the additive increment by the positive starting point and enlarge both ranges. -/
theorem rectangle_to_relative_proved (x h : ℝ) (hh : 1 ≤ h) (hhx : h ≤ x / 4) :
    (∫ u in (0 : ℝ)..(2 * h), ∫ y in (x / 4)..x,
      (Chebyshev.psi (y + u) - Chebyshev.psi y - u) ^ 2) ≤
    x * ∫ δ in (0 : ℝ)..(8 * h / x), State402.Jrelative x δ := by
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  have hU : 0 ≤ 2 * h := by positivity
  have hA : 0 ≤ x / 4 := by positivity
  have hAx : x / 4 ≤ x := by linarith
  have hD : 0 ≤ 8 * h / x := by positivity
  let D := 8 * h / x
  have hD0 : 0 ≤ D := hD
  let F : ℝ → ℝ → ℝ := fun u y => (Chebyshev.psi (y + u) - Chebyshev.psi y - u) ^ 2
  let G : ℝ → ℝ → ℝ := fun δ y =>
    (Chebyshev.psi ((1 + δ) * y) - Chebyshev.psi y - δ * y) ^ 2
  have ha : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc 0 (2 * h))).prod (volume.restrict (Ioc (x / 4) x))) :=
    additive_square_integrable (x / 4) x (2 * h) hA hU
  have hr : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc 0 D)).prod (volume.restrict (Ioc (x / 4) x))) :=
    relative_square_integrable (x / 4) x D hA hx0.le hD
  have hfull : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc 0 D)).prod (volume.restrict (Ioc 0 x))) :=
    relative_square_integrable 0 x D le_rfl hx0.le hD
  have hpoint : ∀ᵐ y ∂volume.restrict (Ioc (x / 4) x),
      (∫ u in Ioc 0 (2 * h), F u y) ≤ x * ∫ δ in Ioc 0 D, G δ y := by
    filter_upwards [hr.prod_left_ae, ae_restrict_mem measurableSet_Ioc] with y hy hyx
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity : 0 < x / 4) hyx.1.le
    have hshort : 0 ≤ 2 * h / y := by positivity
    have hupper : 2 * h / y ≤ D := by
      dsimp [D]
      apply (div_le_div_iff₀ hy0 hx0).mpr
      nlinarith [hyx.1]
    have hscale : (∫ u in (0 : ℝ)..(2 * h), F u y) =
        y * ∫ δ in (0 : ℝ)..(2 * h / y), G δ y := by
      have hc := intervalIntegral.smul_integral_comp_mul_right
        (fun u => F u y) (a := 0) (b := 2 * h / y) y
      rw [zero_mul, div_mul_cancel₀ _ hy0.ne', smul_eq_mul] at hc
      rw [← hc]
      congr 1
      apply intervalIntegral.integral_congr
      intro δ _
      dsimp [F, G]
      rw [show (1 + δ) * y = y + δ * y by ring]
    have hi : IntervalIntegrable (fun δ => G δ y) volume 0 D :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hD).mpr hy
    have hm := intervalIntegral.integral_mono_interval le_rfl hshort hupper
      (Eventually.of_forall (fun δ => show 0 ≤ G δ y from sq_nonneg _)) hi
    have hn : 0 ≤ ∫ δ in (0 : ℝ)..D, G δ y :=
      intervalIntegral.integral_nonneg hD (fun δ _ => sq_nonneg _)
    rw [← intervalIntegral.integral_of_le hU,
      ← intervalIntegral.integral_of_le hD0, hscale]
    exact (mul_le_mul_of_nonneg_left hm hy0.le).trans
      (mul_le_mul_of_nonneg_right hyx.2 hn)
  have hcompare : (∫ y in Ioc (x / 4) x, ∫ δ in Ioc 0 D, G δ y) ≤
      ∫ δ in Ioc 0 D, ∫ y in Ioc 0 x, G δ y := by
    rw [← integral_integral_swap hr]
    apply integral_mono_ae hr.integral_prod_left hfull.integral_prod_left
    filter_upwards [hfull.prod_right_ae] with δ hδ
    exact setIntegral_mono_set hδ (Eventually.of_forall (fun y => sq_nonneg _))
      (Ioc_subset_Ioc hA le_rfl).eventuallySubset
  calc (∫ u in (0 : ℝ)..(2 * h), ∫ y in (x / 4)..x, F u y)
      = ∫ y in Ioc (x / 4) x, ∫ u in Ioc 0 (2 * h), F u y := by
        simp_rw [intervalIntegral.integral_of_le hAx, intervalIntegral.integral_of_le hU]
        exact integral_integral_swap ha
    _ ≤ ∫ y in Ioc (x / 4) x, x * ∫ δ in Ioc 0 D, G δ y :=
      integral_mono_ae ha.integral_prod_right (hr.integral_prod_right.const_mul x) hpoint
    _ = x * (∫ y in Ioc (x / 4) x, ∫ δ in Ioc 0 D, G δ y) := by rw [integral_const_mul]
    _ ≤ x * (∫ δ in Ioc 0 D, ∫ y in Ioc 0 x, G δ y) :=
      mul_le_mul_of_nonneg_left hcompare hx0.le
    _ = x * ∫ δ in (0 : ℝ)..D, State402.Jrelative x δ := by
      simp only [State402.Jrelative, intervalIntegral.integral_of_le hx0.le,
        intervalIntegral.integral_of_le hD0]
      rfl

end LeanLab.GoldbachAverage.Rectangle402
