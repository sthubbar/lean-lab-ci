/-
BHP1997, page 52. Integrating the integer endpoint correction.
Full support containment is retained throughout the integration interval.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp387b

namespace LeanLab.BHP1997.Task387
open Classical Complex MeasureTheory Set

/-- Page 52 normalization. The squared count-to-length center correction
has a genuine integral when the full window stays in the finite support. -/
theorem window_center_length_sq_integrable (S : Finset ℕ) (u : ℂ)
    {z a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hz : 0 ≤ z)
    (hs : ∀ y ∈ Icc a b, Finset.Icc ⌈y⌉₊ ⌊y+y*z⌋₊ ⊆ S) :
    IntervalIntegrable (fun y =>
      ‖windowCenter S u z y-((y*z : ℝ) : ℂ)*u‖^2) volume a b := by
  have hm : Measurable (windowCenter S u z) := by
    change Measurable (fun y : ℝ => ((window S y z).card : ℂ)*u)
    simpa only [window, Finset.sum_const, nsmul_eq_mul] using
      Task308.window_sum_measurable S (fun _ => u) z
  have hf : Measurable (fun y : ℝ =>
      ‖windowCenter S u z y-((y*z : ℝ) : ℂ)*u‖^2) := by fun_prop
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound
    ((measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top)
    hf.aestronglyMeasurable (‖u‖^2)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
  have hy' : y ∈ Icc a b := by
    rw [uIoc_of_le hab] at hy
    exact Ioc_subset_Icc_self hy
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (window_center_length_error (ha.trans hy'.1) hz (hs y hy') u) 2

/-- Page 52 normalization. The integrated squared endpoint correction
is at most the integration length times the squared density norm.
This is an endpoint bound and asserts no logarithmic saving. -/
theorem window_center_length_integral_bound (S : Finset ℕ) (u : ℂ)
    {z a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hz : 0 ≤ z)
    (hs : ∀ y ∈ Icc a b, Finset.Icc ⌈y⌉₊ ⌊y+y*z⌋₊ ⊆ S) :
    (∫ y in a..b, ‖windowCenter S u z y-((y*z : ℝ) : ℂ)*u‖^2) ≤
      (b-a)*‖u‖^2 := by
  have hi := window_center_length_sq_integrable S u ha hab hz hs
  calc
    _ ≤ ∫ y in a..b, ‖u‖^2 :=
      intervalIntegral.integral_mono_on hab hi intervalIntegrable_const (fun y hy =>
        pow_le_pow_left₀ (norm_nonneg _)
          (window_center_length_error (ha.trans hy.1) hz (hs y hy) u) 2)
    _ = (b-a)*‖u‖^2 := by simp

end LeanLab.BHP1997.Task387
