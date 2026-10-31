import LeanLab.LanguascoPerelli1996.Mass108
import LeanLab.LanguascoPerelli1996.Lemma1

/-!
The full cited Lemma 1 of P0071 page 354.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Lemma1Full108
open Real MeasureTheory

/-- Page 354. The zero band sum is continuous after composition with any
continuous positive real function. -/
theorem continuous_zSum_comp {f : ℝ → ℝ} (hf : Continuous f) (hpos : ∀ y, 0 < f y)
    (U T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) :
    Continuous (fun y => zSum (f y) U T q a) := by
  classical
  have hl : Continuous (fun y => Real.log (f y)) := hf.log (fun y => (hpos y).ne')
  have hc : Continuous (fun y => ((Real.log (f y) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hl
  simp_rw [Band108.zSum_eq_sum]
  fun_prop

/-- Page 354. Lemma 1 for the actual sealed zero sum and correlation function. -/
theorem lemma1_verified : Lemma1 := by
  intro _ c C hc hcC
  let K := max |Real.log c| |Real.log C|
  refine ⟨Real.exp (3 * K), ?_⟩
  intro X hX T hT q inst a ha α β hcα hαβ hβC
  have hα : 0 < α := hc.trans_le hcα
  have hβ : 0 < β := hα.trans hαβ
  have hαX : 0 < α * X := mul_pos hα hX
  let g : ℝ → ℝ := fun y => ‖zSum (max (α * X) y) (-1) T q a‖ ^ 2
  have hgc : Continuous g := by
    have hh := continuous_zSum_comp (continuous_const.max continuous_id)
      (fun y => hαX.trans_le (le_max_left _ _)) (-1) T q a
    exact hh.norm.pow 2
  have hg0 : ∀ y, 0 ≤ g y := fun y => sq_nonneg _
  have hclip : (∫ y in α * X..β * X, g y) =
      ∫ y in α * X..β * X, ‖zSum y (-1) T q a‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (mul_le_mul_of_nonneg_right hαβ.le hX.le)] at hy
    dsimp [g]
    rw [max_eq_right hy.1]
  have hclipv : (∫ v in Real.log α..Real.log β,
      g (X * Real.exp v) * Real.exp (-2 * |v|)) =
      ∫ v in Real.log α..Real.log β,
        ‖zSum (X * Real.exp v) (-1) T q a‖ ^ 2 * Real.exp (-2 * |v|) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (Real.log_le_log hα hαβ.le)] at hv
    have he : α ≤ Real.exp v := by
      simpa only [Real.exp_log hα] using Real.exp_le_exp.mpr hv.1
    have hm : α * X ≤ X * Real.exp v := by nlinarith
    dsimp [g]
    rw [max_eq_right hm]
  have hsubst := LeanLab.LanguascoPerelli1996.Lemma1.lemma1 hgc hg0 hX hα hαβ.le
  rw [hclip, hclipv] at hsubst
  have hm : (∫ v in Real.log α..Real.log β,
      ‖zSum (X * Real.exp v) (-1) T q a‖ ^ 2 * Real.exp (-2 * |v|)) ≤ ‖F X T q a‖ := by
    rw [← Mass108.full_weighted_mass hX T q a,
      intervalIntegral.integral_of_le (Real.log_le_log hα hαβ.le)]
    exact setIntegral_le_integral (Correlation108.correlation_identity hX T q a).1
      (Filter.Eventually.of_forall fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hlogbound : ∀ y : ℝ, c ≤ y → y ≤ C → |Real.log y| ≤ K := by
    intro y hcy hyC
    have hy : 0 < y := hc.trans_le hcy
    have hlo := Real.log_le_log hc hcy
    have hhi := Real.log_le_log hy hyC
    apply abs_le.mpr
    constructor
    · have := neg_abs_le (Real.log c)
      have := le_max_left |Real.log c| |Real.log C|
      dsimp [K]
      linarith
    · have := le_abs_self (Real.log C)
      have := le_max_right |Real.log c| |Real.log C|
      dsimp [K]
      linarith
  have he : Real.exp (3 * max |Real.log α| |Real.log β|) ≤ Real.exp (3 * K) := by
    apply Real.exp_le_exp.mpr
    have hh := max_le (hlogbound α hcα (hαβ.le.trans hβC))
      (hlogbound β (hcα.trans hαβ.le) hβC)
    linarith
  calc
    _ ≤ Real.exp (3 * max |Real.log α| |Real.log β|) * X * ‖F X T q a‖ :=
      hsubst.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ ≤ Real.exp (3 * K) * X * ‖F X T q a‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hX.le) (norm_nonneg _)

end LeanLab.LanguascoPerelli1996.Lemma1Full108

namespace LeanLab.LanguascoPerelli1996

/-- CITED. Lemma 1, Section 3. -/
theorem lemma1 : Lemma1 := by
  exact Lemma1Full108.lemma1_verified

end LeanLab.LanguascoPerelli1996
