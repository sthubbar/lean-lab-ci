/-
Supply split for the bare minor family in P0029 page 27, display 7.8.
The single denominator range has the printed logarithm power five.
Only the range with at least two denominators remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp328b

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The logarithm power one bound implies power five uniformly from X two onward. -/
theorem log_le_sixteen_log5_451 {X : ℕ} (hX : 2 ≤ X) :
    Real.log (X : ℝ) ≤ 16 * Real.log X ^ 5 := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ X by exact_mod_cast hX)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by linarith [Real.log_two_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 4
  have hm := mul_le_mul_of_nonneg_right hp (Real.log_natCast_nonneg X)
  norm_num at hm
  nlinarith only [hm]

/-- The bare family needs no minor arc saving when R is below two. -/
theorem minor_bare_single_log1_451 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → (X : ℝ) ^ ϑ < 2 →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X := by
  classical
  obtain ⟨C, hC, hf⟩ := smoothed_family_bound261 hϕ
  refine ⟨2 * C, by positivity, ?_⟩
  intro X hX hR2
  let R : ℝ := (X : ℝ) ^ ϑ
  let W : ℝ → ℂ := fun α => if MajorArc X R α then 0 else 1
  have hW : Measurable W :=
    measurable_const.ite (measurableSet_majorArc84 X R) measurable_const
  have hWB (α : ℝ) : ‖W α‖ ≤ (1 : ℝ) := by
    by_cases hm : MajorArc X R α <;> simp [W, hm]
  have hb := hf X hX W hW 1 (by norm_num) hWB
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) =
        minorBare328 ϕ X N ϑ := by
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases hm : MajorArc X R α <;> simp [W, minorBare328, R, hm]
  simp_rw [heq] at hb
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hXp ϑ
  have hinv : (1 / 2 : ℝ) ≤ R⁻¹ := by
    simpa only [one_div] using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      hRp hR2.le
  have hcoeff : 1 ≤ 2 * (R⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) := by
    have hp : 0 ≤ (X : ℝ) ^ (-(2 / 5) : ℝ) := by positivity
    linarith
  have hh := mul_le_mul_of_nonneg_right hcoeff
    (by positivity : 0 ≤ C * (X : ℝ) ^ 3 * Real.log X)
  change _ ≤ (2 * C) * (R⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
    (X : ℝ) ^ 3 * Real.log X
  nlinarith only [hb, hh]

/-- The bare minor family has the exact printed power five on the single denominator range. -/
theorem minor_bare_single_denominator451 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → (X : ℝ) ^ ϑ < 2 →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, hf⟩ := minor_bare_single_log1_451 hϕ ϑ
  refine ⟨16 * C, by positivity, ?_⟩
  intro X hX hR2
  have hh := mul_le_mul_of_nonneg_left (log_le_sixteen_log5_451 hX)
    (by positivity : 0 ≤ C * (((X : ℝ) ^ ϑ)⁻¹ +
      (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3)
  nlinarith only [hf X hX hR2, hh]

/-- LEAF. P0029 page 27, minor fourth moment step in display 7.8.
OPEN bare minor family restricted to R at least two.
The single denominator range is absent and has a separate clean proof.
The changing N smoothing and printed logarithm power five are retained. -/
theorem minor_bare_multi_denominator451 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- Exact minor_bare_family328 statement from the two disjoint scale ranges.
CONDITIONAL ON minor_bare_multi_denominator451. -/
theorem minor_bare_supply451 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := minor_bare_single_denominator451 hϕ ϑ
  obtain ⟨C₂, hC₂, h₂⟩ := minor_bare_multi_denominator451 hϕ ϑ hϑ hϑ'
  refine ⟨max C₁ C₂, le_trans hC₁ (le_max_left _ _), ?_⟩
  intro X hX
  by_cases hR2 : (X : ℝ) ^ ϑ < 2
  · apply (h₁ X hX hR2).trans
    gcongr
    exact le_max_left _ _
  · apply (h₂ X hX (le_of_not_gt hR2)).trans
    gcongr
    exact le_max_right _ _

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.log_le_sixteen_log5_451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_bare_single_log1_451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_bare_single_denominator451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_bare_multi_denominator451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_bare_supply451
