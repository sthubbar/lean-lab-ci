import LeanLab.GoldbachAverage.GallagherConsequence82

/-!
Concrete and vacuous instances for the new reductions.
P0051 arXiv 2110.14250v2 pages 4 and 20.
The fourth power bound is too weak for Corollary 2.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Instances82
open MeasureTheory Complex
open GSInputs ThetaLayers

/-- A nonvacuous coarse W input with exponent four, valid for all admissible N and h.
This tests the premise of Decomp82.local_of_W without asserting the needed theta bound. -/
theorem W_bound_four : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ h : ℝ, 1 ≤ h → h ≤ N →
    W N h ≤ K * (N : ℝ) ^ (4 : ℝ) * (1 + Real.log N) ^ 4 / h := by
  obtain ⟨K, hK, hb⟩ := theta_lemma1_full_two
  refine ⟨K + 162, by positivity, fun N hN h hh hhN => ?_⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hh0 : 0 < h := by linarith
  set ξ := 1 / (2 * h) with hξdef
  have hξ0 : 0 < ξ := by dsimp [ξ]; positivity
  have hξlo : 1 / (2 * (N : ℝ)) ≤ ξ := by
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hξhi : ξ ≤ 1 / 2 := by
    dsimp [ξ]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hl := hb N hN ξ hξlo hξhi
  norm_num at hl
  have hs := Decomp82.symmetric_integral_eq_W N hN ξ hξ0
  have hwidth : 1 / (2 * ξ) = h := by dsimp [ξ]; field_simp
  rw [hwidth] at hs
  have hN1 : 1 ≤ N := by omega
  have hr0 : 0 < Real.exp (-(1 / (N : ℝ))) := Real.exp_pos _
  have hr1 : Real.exp (-(1 / (N : ℝ))) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := one_div_pos.mpr hN0
    linarith
  have hc1 : IntervalIntegrable (fun α => ‖PsiGen (Real.exp (-(1 / (N : ℝ)))) α -
      IGen (Real.exp (-(1 / (N : ℝ)))) α‖ ^ 2) volume (-ξ) ξ :=
    ((continuous_psi_sub_I hr0 hr1).norm.pow 2).intervalIntegrable _ _
  have hc2 := (LeanLab.LZCesaroShort.continuous_St_sub hN1).intervalIntegrable
    (μ := volume) (-ξ) ξ
  have hm := intervalIntegral.integral_mono_on (show -ξ ≤ ξ by linarith)
    hc1 ((hc2.const_mul 2).add intervalIntegrable_const)
    (fun α (hα : α ∈ Set.Icc (-ξ) ξ) => norm_psi_sub_I_sq_le hN1
      (abs_le.mpr ⟨by linarith [hα.1], by linarith [hα.2]⟩))
  rw [intervalIntegral.integral_add (hc2.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
    hs] at hm
  have hξh : ξ * h = 1 / 2 := by dsimp [ξ]; field_simp
  have hm' := mul_le_mul_of_nonneg_right hm hh0.le
  have hl' := mul_le_mul_of_nonneg_right hl (show 0 ≤ 2 * h by positivity)
  have hp : 1 ≤ (N : ℝ) ^ (4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL : 1 ≤ (1 + Real.log N) ^ 4 := one_le_pow₀ (by linarith)
  have hprod : 1 ≤ (N : ℝ) ^ (4 : ℝ) * (1 + Real.log N) ^ 4 :=
    one_le_mul_of_one_le_of_one_le hp hL
  have he1 : K * (N : ℝ) ^ 4 * ξ * (1 + Real.log N) ^ 4 * (2 * h) =
      K * (N : ℝ) ^ 4 * (1 + Real.log N) ^ 4 := by
    calc _ = (K * (N : ℝ) ^ 4 * (1 + Real.log N) ^ 4) * (2 * (ξ * h)) := by ring
      _ = _ := by rw [hξh]; ring
  rw [he1] at hl'
  have he2 : (2 * (∫ α in (-ξ)..ξ,
      ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ^ 2) +
      (ξ - -ξ) * 162) * h =
      (∫ α in (-ξ)..ξ, ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ^ 2) *
        (2 * h) + 324 * (ξ * h) := by ring
  rw [he2, hξh] at hm'
  have hKP : 0 ≤ K * (N : ℝ) ^ 4 * (1 + Real.log N) ^ 4 := by positivity
  apply (le_div_iff₀ hh0).mpr
  norm_num at *
  nlinarith

/-- RH supplies a vacuous full variance instance, since the strict theta premise is false.
This checks the two cited input parameters of the full variance reduction. -/
theorem full_variance_under_RH (hRH : RiemannHypothesis) : GSFullVariance :=
  Decomp82.full_variance_of_inputs (grosswald_of_RH hRH) (bhms_short_variance_of_RH hRH)

end LeanLab.GoldbachAverage.Instances82
