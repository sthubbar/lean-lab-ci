import Mathlib

/-!
The change of integration order used in P0051 page 11.
A sliding window covers a point for a set of starting positions of length at most h.
The proof reuses Mathlib convolution integrability and its integral identity.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Sliding124
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution

/-- A sliding interval integral is convolution with the backward interval indicator.
Source: P0051 page 11, the change of order for the double integral. -/
theorem window_eq_convolution (f : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    (f ⋆ ((Ico (-h) 0).indicator (fun _ => (1 : ℝ)))) x = ∫ u in x..(x + h), f u := by
  classical
  rw [convolution_def]
  simp only [lsmul_apply, smul_eq_mul]
  have heq : (fun u : ℝ => f u * (Ico (-h) 0).indicator (fun _ => (1 : ℝ)) (x - u)) =
      (Ioc x (x + h)).indicator f := by
    funext u
    by_cases hu : u ∈ Ioc x (x + h)
    · have ht : x - u ∈ Ico (-h) 0 := by
        obtain ⟨h1, h2⟩ := hu
        constructor <;> linarith
      simp only [indicator_of_mem ht, indicator_of_mem hu, mul_one]
    · have ht : x - u ∉ Ico (-h) 0 := by
        intro ht
        apply hu
        obtain ⟨h1, h2⟩ := ht
        constructor <;> linarith
      simp only [indicator_of_notMem ht, indicator_of_notMem hu, mul_zero]
  rw [heq, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith)]

/-- The backward interval indicator has mass h for nonnegative h.
Source: the window multiplicity in P0051 page 11. -/
theorem backward_window_mass {h : ℝ} (hh : 0 ≤ h) :
    (∫ t : ℝ, (Ico (-h) 0).indicator (fun _ => (1 : ℝ)) t) = h := by
  rw [integral_indicator measurableSet_Ico]
  simp [measureReal_def, Real.volume_Ico, hh]

/-- LEAF. P0051 page 11, the valid upper bound in the change of integration order.
The nonnegative half line is bounded by the integral over all starting positions. -/
theorem sliding_integral_le {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ u : ℝ, 0 ≤ f u) {h : ℝ} (hh : 0 ≤ h) :
    (∫ x : ℝ in Ioi 0, ∫ u in x..(x + h), f u) ≤ h * ∫ u : ℝ, f u := by
  classical
  let k : ℝ → ℝ := (Ico (-h) 0).indicator (fun _ => (1 : ℝ))
  have hk : Integrable k := by
    rw [show k = (Ico (-h) 0).indicator (fun _ => (1 : ℝ)) from rfl,
      integrable_indicator_iff measurableSet_Ico]
    exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hk0 : ∀ t, 0 ≤ k t := by
    intro t
    by_cases ht : t ∈ Ico (-h) 0 <;> simp [k, ht]
  have hconv : Integrable (f ⋆ k) := hf.integrable_convolution (L := lsmul ℝ ℝ) hk
  have hconv0 : ∀ x : ℝ, 0 ≤ (f ⋆ k) x := by
    intro x
    rw [convolution_def]
    simp only [lsmul_apply, smul_eq_mul]
    exact integral_nonneg (fun u => mul_nonneg (hf0 u) (hk0 (x - u)))
  have hi := setIntegral_le_integral (s := Ioi (0 : ℝ)) hconv (Eventually.of_forall hconv0)
  have he : ∫ x : ℝ, (f ⋆ k) x = (∫ u : ℝ, f u) * h := by
    rw [integral_convolution (lsmul ℝ ℝ) hf hk]
    simp only [lsmul_apply, smul_eq_mul]
    rw [show (∫ t : ℝ, k t) = h from backward_window_mass hh]
  calc (∫ x : ℝ in Ioi 0, ∫ u in x..(x + h), f u) =
        ∫ x : ℝ in Ioi 0, (f ⋆ k) x := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          exact (window_eq_convolution f hh x).symm
    _ ≤ ∫ x : ℝ, (f ⋆ k) x := hi
    _ = h * ∫ u : ℝ, f u := by rw [he]; ring

/-- P0051 page 11, the positive half line form of the sliding integral upper bound.
Zero extension supplies the globally integrable function used by convolution. -/
theorem positive_sliding_integral_le {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (hf0 : ∀ u : ℝ, 0 < u → 0 ≤ f u) {h : ℝ} (hh : 0 ≤ h) :
    (∫ x : ℝ in Ioi 0, ∫ u in x..(x + h), f u) ≤ h * ∫ u : ℝ in Ioi 0, f u := by
  classical
  let g : ℝ → ℝ := (Ioi 0).indicator f
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr hf
  have hg0 : ∀ u : ℝ, 0 ≤ g u := by
    intro u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · simpa only [g, indicator_of_mem hu] using hf0 u hu
    · simp [g, hu]
  have hb := sliding_integral_le hg hg0 hh
  have heq : (∫ x : ℝ in Ioi 0, ∫ u in x..(x + h), g u) =
      ∫ x : ℝ in Ioi 0, ∫ u in x..(x + h), f u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith : x ≤ x + h)] at hu
    have hu0 : u ∈ Ioi (0 : ℝ) := by have := hx; simp only [mem_Ioi] at *; linarith [hu.1]
    exact indicator_of_mem hu0 f
  rw [heq] at hb
  simpa only [g, integral_indicator measurableSet_Ioi] using hb

/-- Positive translation preserves positive half line integrability.
Source context: P0051 page 11, the shifted endpoint square term. -/
theorem positive_shift_integrable {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    {h : ℝ} (hh : 0 ≤ h) : IntegrableOn (fun x => f (x + h)) (Ioi 0) := by
  classical
  let g : ℝ → ℝ := (Ioi 0).indicator f
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr hf
  have hs := (hg.comp_add_right h).integrableOn (s := Ioi (0 : ℝ))
  apply hs.congr_fun _ measurableSet_Ioi
  intro x hx
  have hxh : x + h ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi] at *; linarith
  exact indicator_of_mem hxh f

/-- A positive translation can only decrease the integral of a nonnegative function
on the positive half line. Source: the shifted endpoint term on P0051 page 11. -/
theorem positive_shift_integral_le {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (hf0 : ∀ u : ℝ, 0 < u → 0 ≤ f u) {h : ℝ} (hh : 0 ≤ h) :
    (∫ x : ℝ in Ioi 0, f (x + h)) ≤ ∫ u : ℝ in Ioi 0, f u := by
  classical
  let g : ℝ → ℝ := (Ioi 0).indicator f
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr hf
  have hg0 : ∀ u : ℝ, 0 ≤ g u := by
    intro u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · simpa only [g, indicator_of_mem hu] using hf0 u hu
    · simp [g, hu]
  have hs := setIntegral_le_integral (s := Ioi (0 : ℝ)) (hg.comp_add_right h)
    (Eventually.of_forall fun x => hg0 (x + h))
  have heq : (∫ x : ℝ in Ioi 0, g (x + h)) = ∫ x : ℝ in Ioi 0, f (x + h) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hxh : x + h ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi] at *; linarith
    exact indicator_of_mem hxh f
  rw [heq, integral_add_right_eq_self (μ := volume) g h] at hs
  simpa only [g, integral_indicator measurableSet_Ioi] using hs

/-- Sliding interval integrals of an integrable positive half line function are integrable
as functions of their positive starting point. Source: P0051 page 11 double integral. -/
theorem positive_sliding_integrable {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    {h : ℝ} (hh : 0 ≤ h) :
    IntegrableOn (fun x : ℝ => ∫ u in x..(x + h), f u) (Ioi 0) := by
  classical
  let g : ℝ → ℝ := (Ioi 0).indicator f
  let k : ℝ → ℝ := (Ico (-h) 0).indicator (fun _ => (1 : ℝ))
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr hf
  have hk : Integrable k := by
    rw [show k = (Ico (-h) 0).indicator (fun _ => (1 : ℝ)) from rfl,
      integrable_indicator_iff measurableSet_Ico]
    exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hc : IntegrableOn (g ⋆ k) (Ioi 0) :=
    (hg.integrable_convolution (L := lsmul ℝ ℝ) hk).integrableOn
  apply hc.congr_fun _ measurableSet_Ioi
  intro x hx
  rw [show (g ⋆ k) x = ∫ u in x..(x + h), g u from window_eq_convolution g hh x]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (by linarith : x ≤ x + h)] at hu
  have hu0 : u ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi] at *; linarith [hu.1]
  exact indicator_of_mem hu0 f

end LeanLab.GoldbachAverage.Sliding124
