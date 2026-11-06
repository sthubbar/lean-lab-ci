/-
P0059 page 7 Lemma 2.5 and source 4, arXiv 1310.6374 page 9.
Finite step-integral partial summation for actual zero ordinates.
The finite identity is auxiliary infrastructure for the displayed Stieltjes identity.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroCounts259

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory

/-- Restricting an interval-integrable function to the right of a cutoff preserves integrability. -/
theorem after_cut_integrable {U V γ : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume U V) :
    IntervalIntegrable (fun t => if γ < t then f t else 0) volume U V := by
  have heq : (fun t => if γ < t then f t else 0) = (Ioi γ).indicator f := by
    funext t
    by_cases ht : γ < t <;> simp [ht]
  rw [heq, intervalIntegrable_iff]
  exact hf.def'.indicator measurableSet_Ioi

/-- The step integral from U to V after a cutoff gamma in that interval equals the integral from gamma to V. -/
theorem integral_after_cut {U V γ : ℝ} {f : ℝ → ℝ}
    (hγ : γ ∈ Icc U V) (hf : IntervalIntegrable f volume U V) :
    (∫ t in U..V, if γ < t then f t else 0) = ∫ t in γ..V, f t := by
  have hUV := hγ.1.trans hγ.2
  have hleft : IntervalIntegrable f volume U γ := hf.mono_set (by
    rw [uIcc_of_le hγ.1, uIcc_of_le hUV]
    exact Icc_subset_Icc le_rfl hγ.2)
  have hright : IntervalIntegrable f volume γ V := hf.mono_set (by
    rw [uIcc_of_le hγ.2, uIcc_of_le hUV]
    exact Icc_subset_Icc hγ.1 le_rfl)
  have hind : IntervalIntegrable ((Iic γ).indicator f) volume U V := by
    rw [intervalIntegrable_iff]
    exact hf.def'.indicator measurableSet_Iic
  calc
    _ = ∫ t in U..V, f t - (Iic γ).indicator f t := by
      apply intervalIntegral.integral_congr
      intro t _
      by_cases h : γ < t
      · simp [h, Set.indicator, not_le.mpr h]
      · simp [h, Set.indicator, le_of_not_gt h]
    _ = (∫ t in U..V, f t) - ∫ t in U..γ, f t := by
      rw [intervalIntegral.integral_sub hf hind]
      congr 1
      convert intervalIntegral.integral_indicator (f := f) (μ := volume) hγ using 1
      apply intervalIntegral.integral_congr
      intro t _
      by_cases ht : t ≤ γ <;> simp [ht]
    _ = _ := by
      have h := intervalIntegral.integral_add_adjacent_intervals hleft hright
      linarith

/-- Integrating a derivative against one ordinate step gives the upper value minus the value at that ordinate. -/
theorem integral_derivative_after_cut {U V γ : ℝ} {φ φ' : ℝ → ℝ}
    (hγ : γ ∈ Icc U V)
    (hd : ∀ t ∈ Icc U V, HasDerivAt φ (φ' t) t)
    (hi : IntervalIntegrable φ' volume U V) :
    (∫ t in U..V, if γ < t then φ' t else 0) = φ V - φ γ := by
  rw [integral_after_cut hγ hi]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hγ.2] at ht
    exact hd t ⟨hγ.1.trans ht.1, ht.2⟩
  · apply hi.mono_set
    rw [uIcc_of_le hγ.2, uIcc_of_le (hγ.1.trans hγ.2)]
    exact Icc_subset_Icc hγ.1 le_rfl

/-- Finite weighted partial summation with a strict ordinate count.
This is the finite version of the Stieltjes step on cited page 9. -/
theorem finite_partial_summation {ι : Type*} (s : Finset ι) (γ w : ι → ℝ)
    {U V : ℝ} {φ φ' : ℝ → ℝ}
    (hγ : ∀ i ∈ s, γ i ∈ Icc U V)
    (hd : ∀ t ∈ Icc U V, HasDerivAt φ (φ' t) t)
    (hi : IntervalIntegrable φ' volume U V) :
    ∑ i ∈ s, w i * φ (γ i) = φ V * (∑ i ∈ s, w i) -
      ∫ t in U..V, (∑ i ∈ s, if γ i < t then w i else 0) * φ' t := by
  classical
  have hint : ∀ i ∈ s, IntervalIntegrable
      (fun t => (if γ i < t then w i else 0) * φ' t) volume U V := by
    intro i _
    simpa only [ite_mul, zero_mul] using after_cut_integrable (γ := γ i) (hi.const_mul (w i))
  have hterm : ∀ i ∈ s,
      (∫ t in U..V, (if γ i < t then w i else 0) * φ' t) =
        w i * (φ V - φ (γ i)) := by
    intro i his
    calc
      _ = ∫ t in U..V, w i * (if γ i < t then φ' t else 0) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        split_ifs <;> simp
      _ = w i * (∫ t in U..V, if γ i < t then φ' t else 0) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by rw [integral_derivative_after_cut (hγ i his) hd hi]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum hint]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.mul_sum]
  simp_rw [mul_sub, mul_comm (φ V)]
  rw [Finset.sum_sub_distrib]
  ring

end LeanLab.KadiriLumley2014.Task399
