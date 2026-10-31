/-
AI wrote this Lean code. Codex task69, 2026-10-25.
An elementary bound for the change of integration range in Lemma 3.2, page 355.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.ModelFormula
import LeanLab.Zinoviev1997.ModelPeriod

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology LeanLab.CircleOrth MeasureTheory

/-- A generic one-sided integral bound for a cubic inverse envelope. -/
theorem tail_piece_le (f : ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hf : Continuous f) (hb : ∀ z ∈ Set.Icc δ (1 / 2 : ℝ),
      ‖f z‖ ≤ 1 / (64 * z ^ 3)) :
    ‖∫ z in δ..(1 / 2 : ℝ), f z‖ ≤ 1 / (128 * δ ^ 2) := by
  have hz : (0 : ℝ) ∉ Set.uIcc δ (1 / 2 : ℝ) := by
    rw [Set.uIcc_of_le hδ']
    intro h
    have := h.1
    linarith
  have hi : IntervalIntegrable (fun z : ℝ => (1 / 64 : ℝ) * z ^ (-3 : ℤ)) volume δ (1 / 2) :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr hz)).const_mul _
  calc
    _ ≤ ∫ z in δ..(1 / 2 : ℝ), ‖f z‖ := intervalIntegral.norm_integral_le_integral_norm hδ'
    _ ≤ ∫ z in δ..(1 / 2 : ℝ), (1 / 64 : ℝ) * z ^ (-3 : ℤ) := by
      apply intervalIntegral.integral_mono_on hδ' (hf.norm.intervalIntegrable _ _) hi
      intro z hzz
      have hh := hb z hzz
      convert hh using 1
      simp only [zpow_neg, zpow_ofNat]
      ring
    _ ≤ _ := by
      rw [intervalIntegral.integral_const_mul,
        integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
      norm_num [zpow_neg, zpow_ofNat]
      field_simp
      nlinarith [sq_nonneg δ]

/-- The reflected model integrand on the centered period. -/
noncomputable def modelKernel (N : ℕ) (z : ℝ) : ℂ :=
  modelSum N z ^ 3 * ee (-((N : ℤ) * z))

theorem continuous_modelKernel (N : ℕ) (hN : 0 < N) : Continuous (modelKernel N) :=
  ((continuous_modelSum hN).pow 3).mul
    (continuous_ee.comp (continuous_const.mul continuous_id).neg)

theorem modelKernel_bound (N : ℕ) (hN : 0 < N) (z : ℝ)
    (hz : 0 < |z|) (hz' : |z| ≤ 1 / 2) :
    ‖modelKernel N z‖ ≤ 1 / (64 * |z| ^ 3) := by
  unfold modelKernel
  rw [norm_mul, norm_ee, mul_one, norm_pow]
  have h := pow_le_pow_left₀ (norm_nonneg _) (modelSum_minor_bound N hN z hz hz') 3
  have he : (1 / (4 * |z|)) ^ 3 = 1 / (64 * |z| ^ 3) := by ring
  rwa [he] at h

/-- The two tails removed from the full centered period. -/
noncomputable def modelTail (N : ℕ) (δ : ℝ) : ℂ :=
  (∫ z in (-1 / 2 : ℝ)..(-δ), modelKernel N z) +
    ∫ z in δ..(1 / 2 : ℝ), modelKernel N z

/-- The integration range error is bounded by one over 64 delta squared. -/
theorem modelTail_norm_le (N : ℕ) (hN : 0 < N) (δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ‖modelTail N δ‖ ≤ 1 / (64 * δ ^ 2) := by
  have hpos : ‖∫ z in δ..(1 / 2 : ℝ), modelKernel N z‖ ≤ 1 / (128 * δ ^ 2) := by
    apply tail_piece_le _ δ hδ hδ' (continuous_modelKernel N hN)
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hδ hz.1
    have h := modelKernel_bound N hN z (by simpa only [abs_of_pos hz0] using hz0)
      (by simpa only [abs_of_pos hz0] using hz.2)
    simpa only [abs_of_pos hz0] using h
  have hneg : ‖∫ z in δ..(1 / 2 : ℝ), modelKernel N (-z)‖ ≤ 1 / (128 * δ ^ 2) := by
    apply tail_piece_le _ δ hδ hδ' ((continuous_modelKernel N hN).comp continuous_neg)
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hδ hz.1
    have h := modelKernel_bound N hN (-z) (by simpa only [abs_neg, abs_of_pos hz0] using hz0)
      (by simpa only [abs_neg, abs_of_pos hz0] using hz.2)
    simpa only [Function.comp_apply, abs_neg, abs_of_pos hz0] using h
  have he : (∫ z in (-1 / 2 : ℝ)..(-δ), modelKernel N z) =
      ∫ z in δ..(1 / 2 : ℝ), modelKernel N (-z) := by
    have h := intervalIntegral.integral_comp_neg (f := modelKernel N)
      (a := δ) (b := (1 / 2 : ℝ))
    simpa only [neg_div] using h.symm
  unfold modelTail
  rw [he]
  have h := (norm_add_le _ _).trans (add_le_add hneg hpos)
  have ha : 1 / (128 * δ ^ 2) + 1 / (128 * δ ^ 2) = 1 / (64 * δ ^ 2) := by ring
  simpa only [ha] using h

/-- The exact decomposition into the central model integral and its two tails. -/
theorem modelIntegral_eq_local_add_tail (N : ℕ) (hN : 0 < N) (δ : ℝ) :
    modelIntegral N = (∫ z in (-δ)..δ, modelKernel N z) + modelTail N δ := by
  have hc := continuous_modelKernel N hN
  have h₁ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-1 / 2) (-δ)) (hc.intervalIntegrable (-δ) δ)
  have h₂ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-1 / 2) δ) (hc.intervalIntegrable δ (1 / 2))
  rw [modelIntegral_centered]
  change (∫ z in (-1 / 2 : ℝ)..(1 / 2 : ℝ), modelKernel N z) = _
  rw [← h₂, ← h₁]
  unfold modelTail
  abel

end LeanLab.Zinoviev1997
