/-
Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4, page 195.
Sectional Cauchy helpers for the exceptional minor strips.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

open MeasureTheory Set Filter Topology Real

namespace LeanLab.Hathi2021.Decomp577a

/-- Helper for Hu page 195. Cauchy for nonnegative real functions with
integrable squares. The measure and its support are arbitrary. -/
theorem integral_mul_le_sqrt_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (∫ x, f x * g x ∂μ) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    hf0 hg0 (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h

/-- Helper for Hu page 195. Integrating one continuous nonnegative
function over a small part of the unit interval costs the square root
of its measure and its full second moment. -/
theorem setIntegral_le_sqrt_measure {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) {s : Set ℝ} (hs : MeasurableSet s)
    (hsI : s ⊆ Icc (0 : ℝ) 1) {m : ℝ} (hm : volume.real s ≤ m) :
    (∫ x in s, f x) ≤
      Real.sqrt (∫ x in Icc (0 : ℝ) 1, f x ^ 2) * Real.sqrt m := by
  have hsq : IntegrableOn (fun x => f x ^ 2) (Icc (0 : ℝ) 1) :=
    (hf.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hmem : MemLp f 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 (hsq.mono_set hsI)
  have hfin : volume s < ⊤ :=
    (measure_mono hsI).trans_lt (by simp)
  letI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hfin.ne
  have hc := integral_mul_le_sqrt_sq hmem (memLp_const (1 : ℝ))
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall (fun _ => zero_le_one))
  have hsquare : (∫ x in s, f x ^ 2) ≤ (∫ x in Icc (0 : ℝ) 1, f x ^ 2) :=
    setIntegral_mono_set hsq (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
      (Filter.Eventually.of_forall hsI)
  calc
    (∫ x in s, f x) ≤ Real.sqrt (∫ x in s, f x ^ 2) * Real.sqrt (volume.real s) := by
      simpa using hc
    _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt hsquare) (Real.sqrt_le_sqrt hm)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Helper for Hu page 195. A sectional Cauchy estimate on the first
minor coordinate. The other coordinate uses its two second moments.
The exceptional set need not be a product set. -/
theorem sectional_cauchy_bound (f g h k : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (hk : Continuous k)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x)
    {D : Set ℝ} (hD : MeasurableSet D) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E)
    {M m : ℝ} (hM : 0 ≤ M)
    (hminor : ∀ x ∈ Icc (0 : ℝ) 1 ∩ D, g x ≤ M)
    (hslice : ∀ y ∈ Icc (0 : ℝ) 1,
      volume.real (Icc (0 : ℝ) 1 ∩ {x | (x, y) ∈ E}) ≤ m) :
    (∫ z in ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ E) ∩ {z | z.1 ∈ D},
      f z.1 * g z.1 * h z.2 * k z.2) ≤
      M * Real.sqrt (∫ x in Icc (0 : ℝ) 1, f x ^ 2) * Real.sqrt m *
        Real.sqrt (∫ y in Icc (0 : ℝ) 1, h y ^ 2) *
        Real.sqrt (∫ y in Icc (0 : ℝ) 1, k y ^ 2) := by
  classical
  let I : Set ℝ := Icc 0 1
  let U : Set (ℝ × ℝ) := I ×ˢ I
  let B : Set (ℝ × ℝ) := E ∩ {z | z.1 ∈ D}
  let F : ℝ × ℝ → ℝ := fun z => f z.1 * g z.1 * h z.2 * k z.2
  let H : ℝ × ℝ → ℝ := B.indicator F
  have hB : MeasurableSet B := hE.inter (hD.preimage measurable_fst)
  have hFc : Continuous F := by dsimp [F]; fun_prop
  have hFi : IntegrableOn F U :=
    hFc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hHi : IntegrableOn H U := hFi.indicator hB
  have hHp : Integrable H ((volume.restrict I).prod (volume.restrict I)) := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod, IntegrableOn, U] using hHi
  have hFub : (∫ z in U ∩ B, F z) = ∫ y in I, ∫ x in I, H (x, y) := by
    rw [← setIntegral_indicator hB]
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using integral_prod_symm H hHp
  let A : ℝ := M * Real.sqrt (∫ x in I, f x ^ 2) * Real.sqrt m
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hinner (y : ℝ) (hy : y ∈ I) : (∫ x in I, H (x, y)) ≤ A * (h y * k y) := by
    let Q : Set ℝ := {x | (x, y) ∈ B}
    let s : Set ℝ := I ∩ Q
    have hQ : MeasurableSet Q := hB.preimage (measurable_id.prodMk measurable_const)
    have hs : MeasurableSet s := measurableSet_Icc.inter hQ
    have hsI : s ⊆ I := inter_subset_left
    have hsE : s ⊆ I ∩ {x | (x, y) ∈ E} := fun x hx => ⟨hx.1, hx.2.1⟩
    have hvol : volume.real s ≤ m :=
      (measureReal_mono hsE ((measure_mono inter_subset_left).trans_lt
        (by simp [I])).ne).trans (hslice y hy)
    have hfg : IntegrableOn (fun x => f x * g x) s :=
      ((hf.mul hg).continuousOn.integrableOn_compact isCompact_Icc).mono_set hsI
    have hMf : IntegrableOn (fun x => M * f x) s :=
      ((hf.const_mul M).continuousOn.integrableOn_compact isCompact_Icc).mono_set hsI
    have hpoint : (∫ x in s, f x * g x) ≤ M * (∫ x in s, f x) := by
      rw [← integral_const_mul]
      apply setIntegral_mono_on hfg hMf hs
      intro x hx
      have hmx := hminor x ⟨hx.1, hx.2.2⟩
      nlinarith [hf0 x]
    have heq : (∫ x in I, H (x, y)) = (∫ x in s, f x * g x) * (h y * k y) := by
      have hid : (fun x => H (x, y)) =
          Q.indicator (fun x => (f x * g x) * (h y * k y)) := by
        funext x
        by_cases hx : (x, y) ∈ B <;> simp [H, F, Q, hx, mul_assoc]
      rw [hid, setIntegral_indicator hQ, integral_mul_const]
    rw [heq]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (hh0 y) (hk0 y))
    apply hpoint.trans
    simpa [A, I, mul_assoc] using mul_le_mul_of_nonneg_left
      (setIntegral_le_sqrt_measure hf hf0 hs hsI hvol) hM
  have hbound : (∫ y in I, ∫ x in I, H (x, y)) ≤ ∫ y in I, A * (h y * k y) := by
    apply setIntegral_mono_on hHp.integral_prod_right
      (((hh.mul hk).const_mul A).continuousOn.integrableOn_compact isCompact_Icc)
      measurableSet_Icc hinner
  have hh2 : MemLp h 2 (volume.restrict I) :=
    (memLp_two_iff_integrable_sq hh.aestronglyMeasurable).2
      ((hh.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  have hk2 : MemLp k 2 (volume.restrict I) :=
    (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).2
      ((hk.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  have hlast := integral_mul_le_sqrt_sq hh2 hk2
    (Filter.Eventually.of_forall hh0) (Filter.Eventually.of_forall hk0)
  have hset : ((I ×ˢ I) ∩ E) ∩ {z | z.1 ∈ D} = U ∩ B := by
    ext z; simp [U, B, and_assoc]
  change (∫ z in ((I ×ˢ I) ∩ E) ∩ {z | z.1 ∈ D}, F z) ≤ _
  rw [hset, hFub]
  calc
    (∫ y in I, ∫ x in I, H (x, y)) ≤ ∫ y in I, A * (h y * k y) := hbound
    _ = A * (∫ y in I, h y * k y) := integral_const_mul _ _
    _ ≤ A * (Real.sqrt (∫ y in I, h y ^ 2) * Real.sqrt (∫ y in I, k y ^ 2)) :=
      mul_le_mul_of_nonneg_left hlast hA
    _ = _ := by dsimp [A, I]; ring

end LeanLab.Hathi2021.Decomp577a
