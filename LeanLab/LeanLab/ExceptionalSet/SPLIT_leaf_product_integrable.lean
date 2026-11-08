import LeanLab.ExceptionalSet.Decomp446b

/-!
Split of the product integrability step of the generic Fourier fold.

A merely periodic `L¹` factor times a kernel of compact Fourier support is
integrable. The proof cuts the real line into unit half open intervals, keeps one
period of the periodic factor on each of them, and is left with the sup norms of
the kernel on the unit intervals, which are summable because an integrable kernel
with compact Fourier support has summable interval sup norms.

The four lemmas marked LEAF below are the open work items; the assembly at the
end of the file derives the target statement from them.
-/

namespace LeanLab.ExceptionalSet.Decomp446b

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck norm_eC)

/-- LEAF. Step 1 of the proof: measurability of the pointwise product. A function
that is periodic of period one and interval integrable over one period is almost
everywhere strongly measurable, a continuous function is strongly measurable, and
a pointwise product of two almost everywhere strongly measurable functions is
almost everywhere strongly measurable. -/
theorem leaf_product_aestronglyMeasurable (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hcont : Continuous K) :
    AEStronglyMeasurable (fun α : ℝ => h α * K α) := by
  have hh_glob : AEStronglyMeasurable h volume := by
    have hcov : ∀ n : ℤ,
        AEStronglyMeasurable h (volume.restrict (Set.Ioc (n : ℝ) ((n : ℝ) + 1))) := by
      intro n
      have hint : IntervalIntegrable h volume (n : ℝ) ((n : ℝ) + 1) :=
        hper.intervalIntegrable₀ (by norm_num) hh _ _
      exact hint.1.1
    have hall := AEStronglyMeasurable.iUnion (μ := volume) (f := h)
      (s := fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1)) hcov
    rwa [iUnion_Ioc_intCast (α := ℝ), Measure.restrict_univ] at hall
  exact hh_glob.mul hcont.aestronglyMeasurable

/-- LEAF. Step 2 of the proof: the unit interval partition of the absolute
integral. The half open unit intervals with integer endpoints are pairwise
disjoint and cover the real line, so the integral of the absolute value of the
product equals the sum over the integers of its integrals over those intervals.
No measurability of the integrand is needed for this step. -/
theorem leaf_lintegral_unit_partition (h K : ℝ → ℂ) :
    ∫⁻ α : ℝ, ENNReal.ofReal ‖h α * K α‖ =
      ∑' n : ℤ, ∫⁻ α in Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖h α * K α‖ := by
  have key := lintegral_iUnion (μ := volume)
    (s := fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1))
    (f := fun α : ℝ => ENNReal.ofReal ‖h α * K α‖)
    (fun n => measurableSet_Ioc) (Set.pairwise_disjoint_Ioc_intCast (α := ℝ))
  rwa [iUnion_Ioc_intCast (α := ℝ), Measure.restrict_univ] at key

/-- LEAF. Step 3 of the proof: the bound on a single unit interval. On the
interval from `n` to `n + 1` the periodic factor takes only its values from one
period, and the continuous kernel is dominated there by the supremum of its norm
on that same interval, so the integral over the interval is at most one period of
the periodic factor times that supremum. -/
theorem leaf_unit_interval_bound (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hcont : Continuous K) (n : ℤ) :
    ∫⁻ α in Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖h α * K α‖ ≤
      (∫⁻ α in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖h α‖) *
        (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) := by
  classical
  -- the periodic factor repeats one period on every unit interval
  have hshift : ∀ α : ℝ, ENNReal.ofReal ‖h (α + (n : ℝ))‖ = ENNReal.ofReal ‖h α‖ := by
    intro α
    rw [show h (α + (n : ℝ)) = h α by simpa using (hper.int_mul n) α]
  have hperiod : ∫⁻ α in Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖h α‖
      = ∫⁻ α in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖h α‖ := by
    rw [← lintegral_indicator measurableSet_Ioc (f := fun α : ℝ => ENNReal.ofReal ‖h α‖),
      ← lintegral_indicator measurableSet_Ioc (f := fun α : ℝ => ENNReal.ofReal ‖h α‖)]
    rw [← lintegral_add_right_eq_self
      (fun α : ℝ => (Set.Ioc (n : ℝ) ((n : ℝ) + 1)).indicator
        (fun α : ℝ => ENNReal.ofReal ‖h α‖) α) (n : ℝ)]
    apply lintegral_congr
    intro α
    have hmem : (α + (n : ℝ) ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1)) ↔
        (α ∈ Set.Ioc (0 : ℝ) 1) := by
      simp only [Set.mem_Ioc]
      constructor <;> intro h' <;> constructor <;> linarith [h'.1, h'.2]
    by_cases hα : α ∈ Set.Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem (hmem.mpr hα), Set.indicator_of_mem hα, hshift]
    · rw [Set.indicator_of_notMem (fun hc => hα (hmem.mp hc)), Set.indicator_of_notMem hα]
  -- the periodic factor is almost everywhere strongly measurable here
  have hfae : AEMeasurable (fun α : ℝ => ENNReal.ofReal ‖h α‖)
      (volume.restrict (Set.Ioc (n : ℝ) ((n : ℝ) + 1))) := by
    have hint : IntervalIntegrable h volume (n : ℝ) ((n : ℝ) + 1) :=
      hper.intervalIntegrable₀ (by norm_num) hh _ _
    exact hint.1.1.norm.aemeasurable.ennreal_ofReal
  calc ∫⁻ α in Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖h α * K α‖
      ≤ ∫⁻ α in Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖h α‖ *
          (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
        rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
        exact mul_le_mul_right
          (le_iSup₂ (f := fun t (_ : t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1)) =>
            ENNReal.ofReal ‖K t‖) α hα) _
    _ = (∫⁻ α in Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖h α‖) *
          (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) :=
        lintegral_mul_const'' _ hfae
    _ = (∫⁻ α in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖h α‖) *
          (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) := by rw [hperiod]

section

open Filter
open scoped FourierTransform ContDiff SchwartzMap Topology

/-- `e` is multiplicative. -/
private lemma eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  rw [eC, eC, eC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The oscillation splits over a difference. -/
private lemma eC_mul_sub (t s ξ : ℝ) :
    eC (ξ * (t - s)) = eC (ξ * t) * eC (-(ξ * s)) := by
  rw [show ξ * (t - s) = ξ * t + -(ξ * s) by ring, eC_add]

/-- `e` is continuous. -/
private lemma continuous_eC : Continuous eC := by
  have h : eC = fun x : ℝ => Complex.exp (2 * ↑π * Complex.I * ↑x) := rfl
  rw [h]
  exact Complex.continuous_exp.comp (by fun_prop)

/-- A smooth cutoff that is one on `[-1,1]` and vanishes outside `[-2,2]`. -/
private lemma exists_chi :
    ∃ χ : ℝ → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ ξ : ℝ, |ξ| ≤ 1 → χ ξ = 1) ∧ (∀ ξ : ℝ, 2 < |ξ| → χ ξ = 0) := by
  set χ : ℝ → ℂ := fun ξ => (Real.smoothTransition (ξ + 2) : ℂ) *
    (Real.smoothTransition (2 - ξ) : ℂ) with hchi_set
  have hzero : ∀ ξ : ℝ, 2 < |ξ| → χ ξ = 0 := by
    intro ξ hξ
    rw [hchi_set]
    show (Real.smoothTransition (ξ + 2) : ℂ) * (Real.smoothTransition (2 - ξ) : ℂ) = 0
    rcases lt_abs.mp hξ with h | h
    · have hz : Real.smoothTransition (2 - ξ) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [hz]
    · have hz : Real.smoothTransition (ξ + 2) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [hz]
  have hone : ∀ ξ : ℝ, |ξ| ≤ 1 → χ ξ = 1 := by
    intro ξ hξ
    rw [hchi_set]
    show (Real.smoothTransition (ξ + 2) : ℂ) * (Real.smoothTransition (2 - ξ) : ℂ) = 1
    rw [abs_le] at hξ
    have h1 : (Real.smoothTransition (ξ + 2) : ℂ) = 1 := by
      rw [Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ ξ + 2)]
      norm_num
    have h2 : (Real.smoothTransition (2 - ξ) : ℂ) = 1 := by
      rw [Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ 2 - ξ)]
      norm_num
    rw [h1, h2, one_mul]
  have hsmooth : ContDiff ℝ ∞ χ := by
    rw [hchi_set]
    exact (Complex.ofRealCLM.contDiff.comp
        (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))).mul
      (Complex.ofRealCLM.contDiff.comp
        (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)))
  have hcpt : HasCompactSupport χ := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) ?_
    intro ξ hξ
    simp only [Set.mem_Icc]
    by_contra h
    rcases not_and_or.mp h with h | h
    · rw [not_le] at h
      exact hξ (hzero ξ (by rw [abs_of_neg (by linarith)]; linarith))
    · rw [not_le] at h
      exact hξ (hzero ξ (by rw [abs_of_pos (by linarith)]; linarith))
  exact ⟨χ, hsmooth, hcpt, hone, hzero⟩

/-- The Schwartz version of the cutoff has the same values. -/
private lemma chi_coe (χ : ℝ → ℂ) (hcpt : HasCompactSupport χ) (hsm : ContDiff ℝ ∞ χ) (ξ : ℝ) :
    (hcpt.toSchwartzMap hsm : ℝ → ℂ) ξ = χ ξ := rfl

/-- The auxiliary weight, written as an integral. -/
private lemma psi_apply (χs : 𝓢(ℝ, ℂ)) (u : ℝ) :
    (((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) u = ∫ ξ, eC (ξ * u) * χs ξ := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with v
  rw [smul_eq_mul]
  congr 1
  simp only [eC]
  congr 1
  push_cast
  ring

/-- Quadratic decay of a Schwartz function. -/
private lemma psi_decay (η : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖(η : ℝ → ℂ) u‖ ≤ C / (1 + |u|) ^ 2 := by
  refine ⟨4 * max (SchwartzMap.seminorm ℂ 0 0 η) (SchwartzMap.seminorm ℂ 2 0 η),
    by positivity, ?_⟩
  intro u
  have h0 : ‖η u‖ ≤ SchwartzMap.seminorm ℂ 0 0 η := SchwartzMap.norm_le_seminorm ℂ η u
  have h2 : ‖u‖ ^ 2 * ‖η u‖ ≤ SchwartzMap.seminorm ℂ 2 0 η :=
    SchwartzMap.norm_pow_mul_le_seminorm ℂ η 2 u
  have hc0 : (0:ℝ) ≤ SchwartzMap.seminorm ℂ 0 0 η := le_trans (norm_nonneg _) h0
  rw [le_div_iff₀ (by positivity : (0:ℝ) < (1 + |u|) ^ 2)]
  rcases le_or_gt |u| 1 with hu | hu
  · have h4 : (1 + |u|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg u]
    have hm := mul_le_mul h0 h4 (by positivity) hc0
    have hle : SchwartzMap.seminorm ℂ 0 0 η ≤
        max (SchwartzMap.seminorm ℂ 0 0 η) (SchwartzMap.seminorm ℂ 2 0 η) := le_max_left _ _
    nlinarith
  · have h4 : (1 + |u|) ^ 2 ≤ 4 * |u| ^ 2 := by nlinarith [abs_nonneg u]
    have hu' : ‖u‖ = |u| := Real.norm_eq_abs u
    rw [hu'] at h2
    have hmul : ‖η u‖ * (1 + |u|) ^ 2 ≤ 4 * (|u| ^ 2 * ‖η u‖) := by
      have hn : (0:ℝ) ≤ ‖η u‖ := norm_nonneg _
      nlinarith
    have hle : SchwartzMap.seminorm ℂ 2 0 η ≤
        max (SchwartzMap.seminorm ℂ 0 0 η) (SchwartzMap.seminorm ℂ 2 0 η) := le_max_right _ _
    nlinarith

/-- The lab Fourier transform is Mathlib's Fourier transform. -/
private lemma ftR_eq_fourier (K : ℝ → ℂ) (a : ℝ) : ftR K a = 𝓕 K a := by
  rw [ftR, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with v
  simp only [eC, smul_eq_mul]
  rw [show Complex.exp (2 * ↑π * Complex.I * ↑(-(a * v)))
        = Complex.exp (↑(-2 * π * v * a) * Complex.I) from by
      congr 1
      push_cast
      ring,
    mul_comm]

/-- The Fourier transform of an integrable function is continuous. -/
private lemma continuous_fourier_of_integrable (K : ℝ → ℂ) (hK : Integrable K) :
    Continuous (𝓕 K) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar continuous_inner hK

/-- A bounded transform support plus integrability makes the transform integrable. -/
private lemma integrable_fourier_of_support (K : ℝ → ℂ) (hK : Integrable K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) : Integrable (𝓕 K) := by
  have hcont : Continuous (𝓕 K) := continuous_fourier_of_integrable K hK
  have hbound : ∀ ξ : ℝ, ‖𝓕 K ξ‖ ≤ ∫ v, ‖K v‖ := fun ξ => norm_fourier_le_integral_norm K ξ
  have hzero : ∀ ξ : ℝ, 1 < |ξ| → 𝓕 K ξ = 0 := by
    intro ξ hξ
    rw [← ftR_eq_fourier K ξ]
    exact hsupp ξ hξ
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt
    (b := ENNReal.ofReal (∫ v, ‖K v‖) * volume (Set.Icc (-1 : ℝ) 1)) ?_ ?_
  · calc ∫⁻ ξ : ℝ, ENNReal.ofReal ‖𝓕 K ξ‖
        ≤ ∫⁻ ξ : ℝ, (Set.Icc (-1 : ℝ) 1).indicator
            (fun _ => ENNReal.ofReal (∫ v, ‖K v‖)) ξ := by
          apply lintegral_mono
          intro ξ
          by_cases hξ : ξ ∈ Set.Icc (-1 : ℝ) 1
          · rw [Set.indicator_of_mem hξ]
            exact ENNReal.ofReal_le_ofReal (hbound ξ)
          · have h2 : 1 < |ξ| := by
              simp only [Set.mem_Icc, not_and_or, not_le] at hξ
              rcases hξ with h | h
              · rw [abs_of_neg (by linarith)]
                linarith
              · rw [abs_of_pos (by linarith)]
                linarith
            rw [Set.indicator_of_notMem hξ]
            simp [hzero ξ h2]
      _ = ENNReal.ofReal (∫ v, ‖K v‖) * volume (Set.Icc (-1 : ℝ) 1) := by
          rw [lintegral_indicator (s := Set.Icc (-1 : ℝ) 1) measurableSet_Icc]
          exact setLIntegral_const _ _
  · rw [Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)

/-- Fourier inversion, in the shape used below. -/
private lemma K_eq_integral_fourier (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hg : Integrable (𝓕 K)) (x : ℝ) : K x = ∫ ξ, eC (x * ξ) * 𝓕 K ξ := by
  have h := MeasureTheory.Integrable.fourierInv_fourier_eq hK hg (v := x) hcont.continuousAt
  rw [← h, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with v
  simp only [eC, smul_eq_mul]
  rw [show Complex.exp (2 * ↑π * Complex.I * ↑(x * v))
        = Complex.exp (↑(-2 * π * v * -x) * Complex.I) from by
      congr 1
      push_cast
      ring]

/-- Reproducing formula: `K` is recovered from its own integral against the auxiliary weight. -/
private lemma reproducing (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0)
    (χs : 𝓢(ℝ, ℂ)) (hχone : ∀ ξ : ℝ, |ξ| ≤ 1 → (χs : ℝ → ℂ) ξ = 1) (t : ℝ) :
    K t = ∫ s, K s * (((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) (t - s) := by
  have hg : Integrable (𝓕 K) := integrable_fourier_of_support K hK hsupp
  have hχint : Integrable (χs : ℝ → ℂ) := χs.integrable
  have hF : Integrable (fun z : ℝ × ℝ => K z.1 * (eC (z.2 * (t - z.1)) * χs z.2))
      (volume.prod volume) := by
    refine Integrable.mono' (g := fun z : ℝ × ℝ => ‖K z.1‖ * ‖χs z.2‖)
      (hK.norm.mul_prod hχint.norm) ?_ ?_
    · refine hK.aestronglyMeasurable.comp_fst.mul ?_
      have : Continuous fun z : ℝ × ℝ => eC (z.2 * (t - z.1)) * χs z.2 :=
        (continuous_eC.comp (by fun_prop : Continuous fun z : ℝ × ℝ => z.2 * (t - z.1))).mul
          (χs.continuous.comp continuous_snd)
      exact this.aestronglyMeasurable
    · filter_upwards with z
      rw [norm_mul, norm_mul, norm_eC, one_mul]
  have hpsi : ∀ u : ℝ, (((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) u = ∫ ξ, eC (ξ * u) * χs ξ :=
    psi_apply χs
  have hA : (∫ s, K s * (((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) (t - s))
      = ∫ s, ∫ ξ, K s * (eC (ξ * (t - s)) * χs ξ) := by
    apply integral_congr_ae
    filter_upwards with s
    rw [hpsi (t - s), ← integral_const_mul]
  have hB : (∫ s, ∫ ξ, K s * (eC (ξ * (t - s)) * χs ξ))
      = ∫ ξ, ∫ s, K s * (eC (ξ * (t - s)) * χs ξ) :=
    integral_integral_swap hF
  have hC : (∫ ξ, ∫ s, K s * (eC (ξ * (t - s)) * χs ξ))
      = ∫ ξ, (∫ s, K s * eC (-(ξ * s))) * (eC (ξ * t) * χs ξ) := by
    apply integral_congr_ae
    filter_upwards with ξ
    rw [show (fun s => K s * (eC (ξ * (t - s)) * χs ξ))
        = (fun s => (K s * eC (-(ξ * s))) * (eC (ξ * t) * χs ξ)) from by
      funext s
      rw [eC_mul_sub]
      ring,
      integral_mul_const]
  have hD : (∫ ξ, (∫ s, K s * eC (-(ξ * s))) * (eC (ξ * t) * χs ξ))
      = ∫ ξ, eC (t * ξ) * 𝓕 K ξ := by
    apply integral_congr_ae
    filter_upwards with ξ
    have hft : (∫ s, K s * eC (-(ξ * s))) = ftR K ξ := rfl
    rw [hft]
    by_cases hξ : |ξ| ≤ 1
    · rw [hχone ξ hξ, mul_one, ftR_eq_fourier, mul_comm ξ t]
      ring
    · have h1 : 1 < |ξ| := lt_of_not_ge hξ
      have hz : ftR K ξ = 0 := hsupp ξ h1
      have hz2 : 𝓕 K ξ = 0 := by
        rw [← ftR_eq_fourier K ξ]
        exact hz
      rw [hz, hz2, zero_mul, mul_zero]
  calc K t = ∫ ξ, eC (t * ξ) * 𝓕 K ξ := K_eq_integral_fourier K hK hcont hg t
    _ = (∫ ξ, (∫ s, K s * eC (-(ξ * s))) * (eC (ξ * t) * χs ξ)) := hD.symm
    _ = (∫ ξ, ∫ s, K s * (eC (ξ * (t - s)) * χs ξ)) := hC.symm
    _ = (∫ s, ∫ ξ, K s * (eC (ξ * (t - s)) * χs ξ)) := hB.symm
    _ = (∫ s, K s * (((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) (t - s)) := hA.symm


/-- A division by something at least one does not increase a nonnegative number. -/
private lemma div_le_self_of_one_le {c b : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b) : c / b ≤ c := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- Partial sums of the telescoping family. -/
private lemma telescope_sum_range (K : ℕ) :
    ∑ k ∈ Finset.range K, ((1:ℝ)/((k:ℝ)+1) - 1/((k:ℝ)+2)) = 1 - 1/((K:ℝ)+1) := by
  induction K with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : (0:ℝ) < (n:ℝ)+1 := by positivity
    have h2 : (0:ℝ) < (n:ℝ)+2 := by positivity
    push_cast
    field_simp
    ring

/-- The telescoping family sums to one. -/
private lemma hasSum_telescope_one :
    HasSum (fun k : ℕ => ((1:ℝ)/((k:ℝ)+1) - 1/((k:ℝ)+2))) 1 := by
  have hnonneg : ∀ k : ℕ, 0 ≤ ((1:ℝ)/((k:ℝ)+1) - 1/((k:ℝ)+2)) := by
    intro k
    have h1 : (0:ℝ) < (k:ℝ)+1 := by positivity
    have h2 : (0:ℝ) < (k:ℝ)+2 := by positivity
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le h1 (by linarith)
  have h' : Tendsto (fun K : ℕ => (1:ℝ) - 1/((K:ℝ)+1)) atTop (𝓝 (1:ℝ)) := by
    have h : Tendsto (fun K : ℕ => (1:ℝ)/((K:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
      have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using h0
    have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 (1:ℝ)) := tendsto_const_nhds
    have h1 := hc.sub h
    simpa using h1
  refine (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).mpr ?_
  simpa only [telescope_sum_range] using h'

/-- `1/(k+1)^2` is summable. -/
private lemma summable_inv_sq_succ : Summable (fun k : ℕ => ((1:ℝ)/((k:ℝ)+1))^2) := by
  have h0 : Summable (fun n : ℕ => (1:ℝ) / (n:ℝ)^2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have h1 : Summable (fun n : ℕ => (1:ℝ) / ((n:ℝ)+1)^2) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ) / (n:ℝ)^2) 1).mpr h0
    simpa [Nat.cast_add, Nat.cast_one] using this
  simpa [div_pow] using h1

/-- `1/(k+1)^2` sums to at most two. -/
private lemma tsum_inv_sq_succ_le_two : (∑' k : ℕ, ((1:ℝ)/((k:ℝ)+1))^2) ≤ 2 := by
  have hcmp : ∀ k : ℕ, ((1:ℝ)/((k:ℝ)+1))^2 ≤ 2 * ((1:ℝ)/((k:ℝ)+1) - 1/((k:ℝ)+2)) := by
    intro k
    have h1 : (0:ℝ) < (k:ℝ)+1 := by positivity
    have h2 : (0:ℝ) < (k:ℝ)+2 := by positivity
    have e1 : ((1:ℝ)/((k:ℝ)+1))^2 = 1/(((k:ℝ)+1)*((k:ℝ)+1)) := by
      field_simp
    have e2 : ((1:ℝ)/((k:ℝ)+1) - 1/((k:ℝ)+2)) = 1/(((k:ℝ)+1)*((k:ℝ)+2)) := by
      field_simp
      ring
    rw [e1, e2, show (2:ℝ) * (1/(((k:ℝ)+1)*((k:ℝ)+2))) = 2/(((k:ℝ)+1)*((k:ℝ)+2)) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsum2 : Summable (fun k : ℕ => 2 * ((1:ℝ)/((k:ℝ)+1) - 1/((k:ℝ)+2))) :=
    hasSum_telescope_one.summable.mul_left 2
  calc (∑' k : ℕ, ((1:ℝ)/((k:ℝ)+1))^2)
      ≤ ∑' k : ℕ, 2 * ((1:ℝ)/((k:ℝ)+1) - 1/((k:ℝ)+2)) :=
        Summable.tsum_le_tsum hcmp summable_inv_sq_succ hsum2
    _ = 2 * (∑' k : ℕ, ((1:ℝ)/((k:ℝ)+1) - 1/((k:ℝ)+2))) := tsum_mul_left
    _ = 2 * 1 := by rw [hasSum_telescope_one.tsum_eq]
    _ ≤ 2 := by norm_num

/-- The positive tail of the integer lattice weight. -/
private lemma summable_lattice_pos (δ : ℝ) (hδ1 : δ < 1) :
    Summable (fun k : ℕ => ((1 + |(k:ℝ) - δ|)^2)⁻¹) := by
  have hcmp : ∀ k : ℕ, ((1 + |(k:ℝ) - δ|)^2)⁻¹ ≤ 4 * ((1:ℝ)/((k:ℝ)+1))^2 := by
    intro k
    have hlow : ((k:ℝ)+1)/2 ≤ 1 + |(k:ℝ) - δ| := by
      rcases le_or_gt k 1 with hk | hk
      · have hk' : (k:ℝ) ≤ 1 := by exact_mod_cast hk
        have : ((k:ℝ)+1)/2 ≤ 1 := by linarith
        linarith [abs_nonneg ((k:ℝ) - δ)]
      · have hk' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.le_of_lt hk
        have h3 : (k:ℝ) - δ ≤ |(k:ℝ) - δ| := le_abs_self _
        linarith
    have hpos : (0:ℝ) < ((k:ℝ)+1)/2 := by positivity
    have hsq : (((k:ℝ)+1)/2)^2 ≤ (1 + |(k:ℝ) - δ|)^2 := pow_le_pow_left₀ (by positivity) hlow 2
    calc ((1 + |(k:ℝ) - δ|)^2)⁻¹ ≤ ((((k:ℝ)+1)/2)^2)⁻¹ := inv_anti₀ (by positivity) hsq
      _ = 4 * ((1:ℝ)/((k:ℝ)+1))^2 := by
          have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
          field_simp
          ring
  exact Summable.of_nonneg_of_le (fun k => by positivity) hcmp (summable_inv_sq_succ.mul_left 4)

/-- The positive tail is at most eight. -/
private lemma tsum_lattice_pos_le (δ : ℝ) (hδ1 : δ < 1) :
    (∑' k : ℕ, ((1 + |(k:ℝ) - δ|)^2)⁻¹) ≤ 8 := by
  have hcmp : ∀ k : ℕ, ((1 + |(k:ℝ) - δ|)^2)⁻¹ ≤ 4 * ((1:ℝ)/((k:ℝ)+1))^2 := by
    intro k
    have hlow : ((k:ℝ)+1)/2 ≤ 1 + |(k:ℝ) - δ| := by
      rcases le_or_gt k 1 with hk | hk
      · have hk' : (k:ℝ) ≤ 1 := by exact_mod_cast hk
        have : ((k:ℝ)+1)/2 ≤ 1 := by linarith
        linarith [abs_nonneg ((k:ℝ) - δ)]
      · have hk' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.le_of_lt hk
        have h3 : (k:ℝ) - δ ≤ |(k:ℝ) - δ| := le_abs_self _
        linarith
    have hsq : (((k:ℝ)+1)/2)^2 ≤ (1 + |(k:ℝ) - δ|)^2 := pow_le_pow_left₀ (by positivity) hlow 2
    calc ((1 + |(k:ℝ) - δ|)^2)⁻¹ ≤ ((((k:ℝ)+1)/2)^2)⁻¹ := inv_anti₀ (by positivity) hsq
      _ = 4 * ((1:ℝ)/((k:ℝ)+1))^2 := by
          have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
          field_simp
          ring
  calc (∑' k : ℕ, ((1 + |(k:ℝ) - δ|)^2)⁻¹)
      ≤ ∑' k : ℕ, 4 * ((1:ℝ)/((k:ℝ)+1))^2 :=
        Summable.tsum_le_tsum hcmp (summable_lattice_pos δ hδ1) (summable_inv_sq_succ.mul_left 4)
    _ = 4 * (∑' k : ℕ, ((1:ℝ)/((k:ℝ)+1))^2) := tsum_mul_left
    _ ≤ 4 * 2 := by
        have := tsum_inv_sq_succ_le_two
        linarith
    _ = 8 := by norm_num

/-- The negative tail of the integer lattice weight. -/
private lemma summable_lattice_neg (δ : ℝ) (hδ0 : 0 ≤ δ) :
    Summable (fun k : ℕ => ((1 + |(-((k:ℝ)+1)) - δ|)^2)⁻¹) := by
  have hcmp : ∀ k : ℕ, ((1 + |(-((k:ℝ)+1)) - δ|)^2)⁻¹ ≤ 4 * ((1:ℝ)/((k:ℝ)+1))^2 := by
    intro k
    have hlow : ((k:ℝ)+1)/2 ≤ 1 + |(-((k:ℝ)+1)) - δ| := by
      have h3 : (k:ℝ)+1+δ ≤ |(-((k:ℝ)+1)) - δ| := by
        have h4 := neg_le_abs ((-((k:ℝ)+1)) - δ)
        rw [show -((-((k:ℝ)+1)) - δ) = (k:ℝ)+1+δ by ring] at h4
        exact h4
      linarith [abs_nonneg ((-((k:ℝ)+1)) - δ)]
    have hsq : (((k:ℝ)+1)/2)^2 ≤ (1 + |(-((k:ℝ)+1)) - δ|)^2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    calc ((1 + |(-((k:ℝ)+1)) - δ|)^2)⁻¹ ≤ ((((k:ℝ)+1)/2)^2)⁻¹ := inv_anti₀ (by positivity) hsq
      _ = 4 * ((1:ℝ)/((k:ℝ)+1))^2 := by
          have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
          field_simp
          ring
  exact Summable.of_nonneg_of_le (fun k => by positivity) hcmp (summable_inv_sq_succ.mul_left 4)

/-- The negative tail is at most eight. -/
private lemma tsum_lattice_neg_le (δ : ℝ) (hδ0 : 0 ≤ δ) :
    (∑' k : ℕ, ((1 + |(-((k:ℝ)+1)) - δ|)^2)⁻¹) ≤ 8 := by
  have hcmp : ∀ k : ℕ, ((1 + |(-((k:ℝ)+1)) - δ|)^2)⁻¹ ≤ 4 * ((1:ℝ)/((k:ℝ)+1))^2 := by
    intro k
    have hlow : ((k:ℝ)+1)/2 ≤ 1 + |(-((k:ℝ)+1)) - δ| := by
      have h3 : (k:ℝ)+1+δ ≤ |(-((k:ℝ)+1)) - δ| := by
        have h4 := neg_le_abs ((-((k:ℝ)+1)) - δ)
        rw [show -((-((k:ℝ)+1)) - δ) = (k:ℝ)+1+δ by ring] at h4
        exact h4
      linarith [abs_nonneg ((-((k:ℝ)+1)) - δ)]
    have hsq : (((k:ℝ)+1)/2)^2 ≤ (1 + |(-((k:ℝ)+1)) - δ|)^2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    calc ((1 + |(-((k:ℝ)+1)) - δ|)^2)⁻¹ ≤ ((((k:ℝ)+1)/2)^2)⁻¹ := inv_anti₀ (by positivity) hsq
      _ = 4 * ((1:ℝ)/((k:ℝ)+1))^2 := by
          have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
          field_simp
          ring
  calc (∑' k : ℕ, ((1 + |(-((k:ℝ)+1)) - δ|)^2)⁻¹)
      ≤ ∑' k : ℕ, 4 * ((1:ℝ)/((k:ℝ)+1))^2 :=
        Summable.tsum_le_tsum hcmp (summable_lattice_neg δ hδ0) (summable_inv_sq_succ.mul_left 4)
    _ = 4 * (∑' k : ℕ, ((1:ℝ)/((k:ℝ)+1))^2) := tsum_mul_left
    _ ≤ 8 := by
        have := tsum_inv_sq_succ_le_two
        linarith



/-- Summability of the shifted integer lattice weight. -/
private lemma summable_lattice_shift (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    Summable (fun m : ℤ => ((1 + |(m:ℝ) - δ|)^2)⁻¹) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using summable_lattice_pos δ hδ1
  · simpa using summable_lattice_neg δ hδ0

/-- The integer lattice weight is summable, with a bound uniform in the shift. -/
private lemma lattice_bounds (s : ℝ) :
    Summable (fun n : ℤ => ((1 + |(n:ℝ) - s|)^2)⁻¹) ∧
      (∑' n : ℤ, ((1 + |(n:ℝ) - s|)^2)⁻¹) ≤ 20 := by
  set M : ℤ := ⌊s⌋ with hM
  have hδ0 : 0 ≤ s - (M:ℝ) := by rw [hM]; linarith [Int.floor_le s]
  have hδ1 : s - (M:ℝ) < 1 := by rw [hM]; linarith [Int.lt_floor_add_one s]
  set f : ℤ → ℝ := fun n => ((1 + |(n:ℝ) - s|)^2)⁻¹ with hf
  set g : ℤ → ℝ := fun m => ((1 + |(m:ℝ) - (s - (M:ℝ))|)^2)⁻¹ with hg
  have hterm : ∀ m : ℤ, f (m + M) = g m := by
    intro m
    show ((1 + |((m + M : ℤ) : ℝ) - s|)^2)⁻¹
      = ((1 + |(m:ℝ) - (s - (M:ℝ))|)^2)⁻¹
    have harg : ((m + M : ℤ) : ℝ) - s = (m:ℝ) - (s - (M:ℝ)) := by push_cast; ring
    rw [harg]
  have hgsum : Summable g := summable_lattice_shift (s - (M:ℝ)) hδ0 hδ1
  have hfsum : Summable f := by
    have h2 : Summable (fun m : ℤ => f (m + M)) := by
      refine hgsum.congr ?_
      intro m
      exact (hterm m).symm
    have h2' : Summable (f ∘ (Equiv.addRight M)) := by
      simpa [Function.comp_def] using h2
    exact (Equiv.summable_iff (Equiv.addRight M)).mp h2'
  have hval : (∑' n : ℤ, f n) = ∑' m : ℤ, g m := by
    rw [← Equiv.tsum_eq (Equiv.addRight M) f]
    exact tsum_congr hterm
  refine ⟨hfsum, ?_⟩
  rw [hval, hg]
  have hp : Summable (fun n : ℕ => ((1 + |(n:ℝ) - (s - (M:ℝ))|)^2)⁻¹) :=
    summable_lattice_pos (s - (M:ℝ)) hδ1
  have hn : Summable (fun n : ℕ => ((1 + |(-((n:ℝ)+1)) - (s - (M:ℝ))|)^2)⁻¹) :=
    summable_lattice_neg (s - (M:ℝ)) hδ0
  have hsplit : (∑' m : ℤ, ((1 + |(m:ℝ) - (s - (M:ℝ))|)^2)⁻¹)
      = (∑' n : ℕ, ((1 + |(n:ℝ) - (s - (M:ℝ))|)^2)⁻¹)
        + (∑' n : ℕ, ((1 + |(-((n:ℝ)+1)) - (s - (M:ℝ))|)^2)⁻¹) := by
    have h := tsum_of_nat_of_neg_add_one (f := fun m : ℤ => ((1 + |(m:ℝ) - (s - (M:ℝ))|)^2)⁻¹)
      (by simpa using hp) (by simpa using hn)
    rw [h]
    simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one]
  rw [hsplit]
  have h1 := tsum_lattice_pos_le (s - (M:ℝ)) hδ1
  have h2 := tsum_lattice_neg_le (s - (M:ℝ)) hδ0
  linarith

/-- The oscillation weight is bounded by a quadratic lattice weight. -/
private lemma psi_env (χs : 𝓢(ℝ, ℂ)) (Cψ : ℝ) (hCψ0 : 0 ≤ Cψ) (hCψbd : ∀ u : ℝ,
      ‖(((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) u‖ ≤ Cψ / (1 + |u|) ^ 2) :
    ∀ (n : ℤ) (t s : ℝ), t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1) →
      ‖(((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) (t - s)‖ ≤ 4 * Cψ * ((1 + |(n : ℝ) - s|)^2)⁻¹ := by
  intro n t s ht
  have ht1 : (n:ℝ) < t := ht.1
  have ht2 : t ≤ (n:ℝ) + 1 := ht.2
  have hdec := hCψbd (t - s)
  have hhalf : (1 + |(n:ℝ) - s|)/2 ≤ 1 + |t - s| := by
    have habs : |(n:ℝ) - s| ≤ |t - s| + 1 := by
      have he : (n:ℝ) - s = (t - s) + ((n:ℝ) - t) := by ring
      rw [he]
      refine le_trans (abs_add_le _ _) ?_
      have hnt : |(n:ℝ) - t| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      linarith
    have hts : (0:ℝ) ≤ |t - s| := abs_nonneg _
    linarith
  have hsq : ((1 + |(n:ℝ) - s|)/2)^2 ≤ (1 + |t - s|)^2 := pow_le_pow_left₀ (by positivity) hhalf 2
  calc ‖(((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) (t - s)‖ ≤ Cψ * ((1 + |t - s|)^2)⁻¹ := by
        simpa [div_eq_mul_inv] using hdec
    _ ≤ Cψ * (((1 + |(n:ℝ) - s|)/2)^2)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ hCψ0
        exact inv_anti₀ (by positivity) hsq
    _ = 4 * Cψ * ((1 + |(n:ℝ) - s|)^2)⁻¹ := by
        have h1 : (0:ℝ) < 1 + |(n:ℝ) - s| := by linarith [abs_nonneg ((n:ℝ) - s)]
        field_simp
        ring

/-- The interval supremum of `K` is controlled by the lattice weight. -/
private lemma interval_step (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (χs : 𝓢(ℝ, ℂ))
    (hχone : ∀ ξ : ℝ, |ξ| ≤ 1 → (χs : ℝ → ℂ) ξ = 1)
    (Cψ : ℝ) (hCψ0 : 0 ≤ Cψ)
    (hCψbd : ∀ u : ℝ, ‖(((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) u‖ ≤ Cψ / (1 + |u|) ^ 2) :
    ∀ n : ℤ, (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≤
      ∫⁻ s, ENNReal.ofReal ‖K s‖ *
        ENNReal.ofReal (4 * Cψ * ((1 + |(n : ℝ) - s|)^2)⁻¹) := by
  intro n
  have hpoint : ∀ t : ℝ, ‖K t‖ ≤
      ∫ s, ‖K s‖ * ‖(((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) (t - s)‖ := by
    intro t
    rw [reproducing K hK hcont hsupp χs hχone t]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    filter_upwards with s
    rw [norm_mul]
  apply iSup₂_le
  intro t ht
  refine le_trans (ENNReal.ofReal_le_ofReal (hpoint t)) ?_
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => ‖(((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) (t - s)‖) :=
    ((𝓕⁻ χs : 𝓢(ℝ, ℂ)).continuous.comp
      (continuous_const.sub continuous_id)).norm.aestronglyMeasurable
  have hbound : ∀ᵐ s : ℝ, ‖‖(((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) (t - s)‖‖ ≤ Cψ := by
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine le_trans (hCψbd (t - s)) (div_le_self_of_one_le hCψ0 ?_)
    nlinarith [abs_nonneg (t - s)]
  have hint : Integrable (fun s : ℝ => ‖K s‖ * ‖(((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) (t - s)‖) :=
    hK.norm.mul_bdd hmeas hbound
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun s => by positivity))]
  apply lintegral_mono
  intro s
  simp only []
  rw [show ENNReal.ofReal (‖K s‖ * ‖(((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) (t - s)‖)
      = ENNReal.ofReal ‖K s‖ * ENNReal.ofReal ‖(((𝓕⁻ χs : 𝓢(ℝ, ℂ))) : ℝ → ℂ) (t - s)‖
      from ENNReal.ofReal_mul (norm_nonneg _)]
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (psi_env χs Cψ hCψ0 hCψbd n t s ht)) _



/-- The weights are summable. -/
private lemma weights_summable (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≠ ⊤ := by
  obtain ⟨χ, hsm, hcpt, hχone, hχzero⟩ := exists_chi
  set χs : 𝓢(ℝ, ℂ) := hcpt.toSchwartzMap hsm with hχs
  have hχone' : ∀ ξ : ℝ, |ξ| ≤ 1 → (χs : ℝ → ℂ) ξ = 1 := by
    intro ξ hξ
    rw [show (χs : ℝ → ℂ) ξ = χ ξ from chi_coe χ hcpt hsm ξ]
    exact hχone ξ hξ
  obtain ⟨Cψ, hCψ0, hCψbd⟩ := psi_decay (𝓕⁻ χs)
  have hKmeas : AEMeasurable (fun s : ℝ => ENNReal.ofReal ‖K s‖) volume :=
    hK.aestronglyMeasurable.aemeasurable.norm.ennreal_ofReal
  have hW : ∀ s : ℝ, (∑' n : ℤ, ENNReal.ofReal (4 * Cψ * ((1 + |(n:ℝ) - s|)^2)⁻¹))
      ≤ ENNReal.ofReal (80 * Cψ) := by
    intro s
    obtain ⟨hsumm, hbound⟩ := lattice_bounds s
    calc (∑' n : ℤ, ENNReal.ofReal (4 * Cψ * ((1 + |(n:ℝ) - s|)^2)⁻¹))
        = ENNReal.ofReal (4 * Cψ) *
            (∑' n : ℤ, ENNReal.ofReal (((1 + |(n:ℝ) - s|)^2)⁻¹)) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun n => ?_
          exact ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (4 * Cψ) *
            ENNReal.ofReal (∑' n : ℤ, ((1 + |(n:ℝ) - s|)^2)⁻¹) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
      _ ≤ ENNReal.ofReal (4 * Cψ) * ENNReal.ofReal 20 := by gcongr
      _ = ENNReal.ofReal (80 * Cψ) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hmain : (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖)
      ≤ ENNReal.ofReal (80 * Cψ) * ∫⁻ s, ENNReal.ofReal ‖K s‖ := by
    calc (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖)
        ≤ ∑' n : ℤ, ∫⁻ s, ENNReal.ofReal ‖K s‖ *
            ENNReal.ofReal (4 * Cψ * ((1 + |(n:ℝ) - s|)^2)⁻¹) :=
          ENNReal.tsum_le_tsum (interval_step K hK hcont hsupp χs hχone' Cψ hCψ0 hCψbd)
      _ = ∫⁻ s, ∑' n : ℤ, ENNReal.ofReal ‖K s‖ *
            ENNReal.ofReal (4 * Cψ * ((1 + |(n:ℝ) - s|)^2)⁻¹) := by
          have hmeas : ∀ n : ℤ, AEMeasurable (fun s : ℝ => ENNReal.ofReal ‖K s‖ *
              ENNReal.ofReal (4 * Cψ * ((1 + |(n:ℝ) - s|)^2)⁻¹)) volume := by
            intro n
            have h2 : AEMeasurable
                (fun s : ℝ => ENNReal.ofReal (4 * Cψ * ((1 + |(n:ℝ) - s|) ^ 2)⁻¹)) volume := by
              measurability
            exact hKmeas.mul h2
          exact (lintegral_tsum hmeas).symm
      _ = ∫⁻ s, ENNReal.ofReal ‖K s‖ *
            (∑' n : ℤ, ENNReal.ofReal (4 * Cψ * ((1 + |(n:ℝ) - s|)^2)⁻¹)) := by
          apply lintegral_congr
          intro s
          exact ENNReal.tsum_mul_left
      _ ≤ ∫⁻ s, ENNReal.ofReal ‖K s‖ * ENNReal.ofReal (80 * Cψ) := by
          apply lintegral_mono
          intro s
          simp only []
          exact mul_le_mul_right (hW s) _
      _ = ENNReal.ofReal (80 * Cψ) * ∫⁻ s, ENNReal.ofReal ‖K s‖ := by
          rw [lintegral_mul_const'' _ hKmeas, mul_comm]
  have hfin : ∫⁻ s, ENNReal.ofReal ‖K s‖ < ⊤ := (hasFiniteIntegral_iff_norm K).mp hK.2
  exact ne_of_lt (lt_of_le_of_lt hmain (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin))


end

/-- LEAF. Step 4 of the proof: the weights are summable. For an integrable
continuous kernel whose Fourier transform vanishes outside the interval from `-1`
to `1`, the supremum of its norm over the unit interval starting at `n` is a
summable function of the integer `n`. This is the analytic input of the split: it
is a statement about the kernel alone and does not mention the periodic factor. -/
theorem leaf_kernel_sup_summable (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≠ ⊤ :=
  weights_summable K hK hcont hsupp

/-- Assembly. Product integrability from the four steps above: measure the
product, split the absolute integral over the unit intervals, bound each piece by
one period of the periodic factor times the kernel supremum on that interval, and
sum the resulting weights. -/
theorem leaf_product_integrable_split (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    Integrable (fun α : ℝ => h α * K α) := by
  refine ⟨leaf_product_aestronglyMeasurable h K hper hh hcont, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hC : (∫⁻ α in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖h α‖) ≠ ⊤ := by
    have h := hh.1.2
    rw [hasFiniteIntegral_iff_norm] at h
    simpa only [IntegrableOn] using h.ne
  have hsup : (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≠ ⊤ :=
    leaf_kernel_sup_summable K hK hcont hsupp
  calc
    ∫⁻ α, ENNReal.ofReal ‖h α * K α‖
        = ∑' n : ℤ,
            ∫⁻ α in Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖h α * K α‖ :=
          leaf_lintegral_unit_partition h K
    _ ≤ ∑' n : ℤ, (∫⁻ α in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖h α‖) *
            (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) :=
          ENNReal.tsum_le_tsum fun n => leaf_unit_interval_bound h K hper hh hcont n
    _ = (∫⁻ α in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖h α‖) *
          ∑' n : ℤ, (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) :=
          ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) (lt_top_iff_ne_top.mpr hsup)

end LeanLab.ExceptionalSet.Decomp446b
