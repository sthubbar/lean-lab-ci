import LeanLab.ExceptionalSet.Decomp450a

/-!
P0082 page 356, first proof display of Lemma 1.
Source: https://doi.org/10.5802/aif.1621
Local absolute convergence of kernel translates also supplies product integrability.
This connects the fold and Poisson steps to one convergence input.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp450b

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck norm_eC)

/-- P0082 page 356, integrability justification for the first proof display.
A periodic function integrable on one period can be multiplied by a continuous
kernel with summable translate sup norms on the unit interval. -/
theorem product_integrable_of_translate_norm (h K : ℝ → ℂ)
    (hper : Function.Periodic h 1) (hh : IntervalIntegrable h volume 0 1)
    (hcont : Continuous K)
    (hnorm : Summable (fun n : ℤ =>
      ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict
        (Set.Icc 0 1)‖)) :
    Integrable (fun x : ℝ => h x * K x) := by
  let c : ℤ → ℝ := fun n =>
    ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict
      (Set.Icc 0 1)‖
  have hperiod (n : ℤ) (x : ℝ) : h (x + n) = h x := by
    simpa only [mul_one] using hper.int_mul n x
  have hhn (n : ℤ) : IntervalIntegrable h volume (n : ℝ) (n + 1) := by
    have hi := hh.comp_add_right (-(n : ℝ))
    simp only [show (fun x : ℝ => h (x + -(n : ℝ))) = h from
      funext (fun x => by simpa only [Int.cast_neg] using hperiod (-n) x)] at hi
    convert hi using 1 <;> ring
  have hgn (n : ℤ) : IntegrableOn (fun x : ℝ => h x * K x)
      (Set.Ioc (n : ℝ) (n + 1)) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      ((hhn n).mul_continuousOn hcont.continuousOn)
  have hbound (n : ℤ) (x : ℝ) (hx : x ∈ Set.Ioc (n : ℝ) (n + 1)) : ‖K x‖ ≤ c n := by
    have hb := (((⟨K, hcont⟩ : C(ℝ, ℂ)).comp
      (ContinuousMap.addRight (n : ℝ))).restrict (Set.Icc 0 1)).norm_coe_le_norm
        ⟨x - n, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
    simpa only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, ContinuousMap.coe_addRight, sub_add_cancel] using hb
  have hintegral (n : ℤ) :
      (∫ x in Set.Ioc (n : ℝ) (n + 1), ‖h x‖) = ∫ x in (0 : ℝ)..1, ‖h x‖ := by
    rw [← intervalIntegral.integral_of_le (by linarith : (n : ℝ) ≤ n + 1)]
    have hi := intervalIntegral.integral_comp_add_right (fun x : ℝ => ‖h x‖) (n : ℝ)
      (a := 0) (b := 1)
    rw [show (1 : ℝ) + n = n + 1 by ring] at hi
    simpa only [zero_add, hperiod] using hi.symm
  have hs : Summable (fun n : ℤ =>
      ∫ x in Set.Ioc (n : ℝ) (n + 1), ‖h x * K x‖) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
      (fun n => ?_) (hnorm.mul_left (∫ x in (0 : ℝ)..1, ‖h x‖))
    calc
      _ ≤ ∫ x in Set.Ioc (n : ℝ) (n + 1), ‖h x‖ * c n := by
        apply setIntegral_mono_on (hgn n).norm
          (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp (hhn n)).norm.mul_const _)
          measurableSet_Ioc
        intro x hx
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound n x hx) (norm_nonneg _)
      _ = (∫ x in (0 : ℝ)..1, ‖h x‖) * c n := by
        rw [integral_mul_const, hintegral]
  have hi := integrableOn_iUnion_of_summable_integral_norm hgn hs
  simpa only [iUnion_Ioc_intCast, integrableOn_univ] using hi

/-- P0082 page 356, exact inherited product integrability leaf.
This supply is CONDITIONAL ON the smaller translate convergence leaf. -/
theorem product_integrable_assembly (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    Integrable (fun α : ℝ => h α * K α) := by
  exact product_integrable_of_translate_norm h K hper hh hcont
    (Decomp450a.leaf_translate_norm K hK hcont hsupp ⟨Set.Icc 0 1, isCompact_Icc⟩)

/-- P0082 page 356, exact sealed fold statement from the same convergence input.
The integral exchange itself is the proved fold_of_integrable theorem. -/
theorem fold_assembly (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    (∫ α, h α * K α * eC (-(α * v))) =
      ∫ α in (0 : ℝ)..1,
        h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) := by
  apply Decomp404b.fold_of_integrable h K hper v
  have he : Continuous (fun α : ℝ => eC (-(α * v))) := by unfold eC; fun_prop
  exact (product_integrable_assembly h K hper hh hK hcont hsupp).mul_bdd
    he.aestronglyMeasurable (Filter.Eventually.of_forall (fun α => (norm_eC _).le))

/-- P0082 page 356, generic Lemma 1 with its convergence hypothesis explicit.
This implication uses no admitted fold, Poisson or product integrability statement. -/
theorem lemma1_of_translate_norm (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0)
    (hnorm : ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ =>
        ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖))
    (v : ℝ) :
    (∫ α, h α * K α * eC (-(α * v))) =
      ftR K (Int.fract v) * hcheck h ⌊v⌋ +
        ftR K (Int.fract v - 1) * hcheck h (⌊v⌋ + 1) := by
  have hg0 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * (⌊v⌋ : ℝ)))) volume 0 1 := by
    apply hh.mul_continuousOn
    unfold eC
    fun_prop
  have hg1 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) volume 0 1 := by
    apply hh.mul_continuousOn
    unfold eC
    fun_prop
  calc
    _ = ∫ α in (0 : ℝ)..1,
        (h α * eC (-(α * (⌊v⌋ : ℝ)))) * ftR K (Int.fract v) +
          (h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) * ftR K (Int.fract v - 1) := by
      rw [Decomp404b.fold_of_integrable h K hper v (by
        have he : Continuous (fun x : ℝ => eC (-(x * v))) := by unfold eC; fun_prop
        exact (product_integrable_of_translate_norm h K hper hh hcont
          (hnorm ⟨Set.Icc 0 1, isCompact_Icc⟩)).mul_bdd he.aestronglyMeasurable
            (Filter.Eventually.of_forall (fun x => (norm_eC _).le)))]
      apply intervalIntegral.integral_congr
      intro α hα
      dsimp only
      rw [Decomp450a.summation_of_translate_norm K hK hcont hsupp hnorm v α,
        Decomp371d.leaf_poisson_collapse K hK hcont hsupp v α]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (hg0.mul_const (ftR K (Int.fract v)))
        (hg1.mul_const (ftR K (Int.fract v - 1))),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      unfold hcheck
      ring


/-- P0082 page 356, exact generic Lemma 1 from one smaller convergence leaf.
Neither the original fold leaf nor any original Poisson admission is used. -/
theorem lemma1_assembly : LeanLab.ExceptionalSet.U1539.Lemma1 := by
  intro h K hper hh hK hcont hsupp v
  exact lemma1_of_translate_norm h K hper hh hK hcont hsupp
    (Decomp450a.leaf_translate_norm K hK hcont hsupp) v

/-- P0082 pages 356 and 357, full Lemma 1 for the explicit paper kernel.
This allows every periodic L1 function h and uses no open generic convergence leaf.
The Delta range is extended to the range of the existing kernel transform theorem. -/
theorem kernel_lemma1 (h : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α, h α * (LeanLab.ExceptionalSet.U1539.Kfun Δ α : ℂ) * eC (-(α * v))) =
      (KernelTransform264.weight Δ (Int.fract v) : ℂ) * hcheck h ⌊v⌋ +
        (KernelTransform264.weight Δ (Int.fract v - 1) : ℂ) * hcheck h (⌊v⌋ + 1) := by
  have hsupp (α : ℝ) (hα : 1 < |α|) :
      ftR (fun x : ℝ => (LeanLab.ExceptionalSet.U1539.Kfun Δ x : ℂ)) α = 0 :=
    KernelTransform264.ftR_Kfun_zero hΔ hΔ1 hα.le
  have hi := lemma1_of_translate_norm h _ hper hh
    (KernelTransform264.Kfun_integrable hΔ hΔ1) (KernelTransform264.Kfun_continuous Δ)
    hsupp (Decomp450a.kernel_translate_norm Δ hΔ hΔ1) v
  simpa only [KernelTransform264.ftR_Kfun hΔ hΔ1] using hi

end LeanLab.ExceptionalSet.Decomp450b
