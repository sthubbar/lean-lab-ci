/-
MMS https://arxiv.org/abs/1610.02017v2, pages 11 and 12.
Separate the two terms of equation 5.1 before taking their weighted means.
The two remaining asymptotics require uniform rough number estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp571a

namespace LeanLab.Ternary.MMS.Task571
open Finset MeasureTheory

/-- The weighted mean of the first rough indicator in equation 5.1.
MMS page 11 bottom display, with only the first term retained. -/
noncomputable def roughReferenceMean (x : ℝ) : ℝ :=
  Real.log x *
    (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n * Task361.roughIndicator n (x ^ (1 / 4 : ℝ))) /
    (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)

/-- The weighted mean of the ordered triple correction in equation 5.1.
MMS page 11. Subtracting the first indicator gives exactly that finite triple sum. -/
noncomputable def correctionReferenceMean (x : ℝ) : ℝ :=
  Real.log x *
    (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n *
        (Task361.harmanMajorant x n - Task361.roughIndicator n (x ^ (1 / 4 : ℝ)))) /
    (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)

/-- The two weighted means add to the exact sealed reference mean.
MMS page 11 equation 5.1 and bottom display. No analytic input is used. -/
theorem referenceMean_split (x : ℝ) :
    Task379.referenceMean x = roughReferenceMean x + correctionReferenceMean x := by
  unfold Task379.referenceMean roughReferenceMean correctionReferenceMean
  simp_rw [mul_sub, sum_sub_distrib]
  ring

/-- The finite ordered triple correction is nonnegative.
MMS page 11 equation 5.1. -/
theorem harman_correction_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ Task361.harmanMajorant x n - Task361.roughIndicator n (x ^ (1 / 4 : ℝ)) := by
  classical
  unfold Task361.harmanMajorant
  rw [add_sub_cancel_left]
  apply sum_nonneg
  intro p₁ hp₁
  apply sum_nonneg
  intro p₂ hp₂
  apply sum_nonneg
  intro p₃ hp₃
  split_ifs
  · exact Task361.roughIndicator_nonneg _ _
  · exact le_rfl

/-- The normalized rough reference mean is nonnegative for x at least one.
Derived sign check for MMS page 11 bottom display. -/
theorem roughReferenceMean_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ roughReferenceMean x := by
  unfold roughReferenceMean
  apply div_nonneg
  · apply mul_nonneg (Real.log_nonneg hx)
    apply sum_nonneg
    intro n hn
    exact mul_nonneg (Task379.referenceWeight_nonneg x n) (Task361.roughIndicator_nonneg _ _)
  · exact (Task379.referenceWeight_integral_pos (by linarith)).le

/-- The normalized correction reference mean is nonnegative for x at least one.
Derived sign check for MMS page 11 bottom display. -/
theorem correctionReferenceMean_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ correctionReferenceMean x := by
  unfold correctionReferenceMean
  apply div_nonneg
  · apply mul_nonneg (Real.log_nonneg hx)
    apply sum_nonneg
    intro n hn
    exact mul_nonneg (Task379.referenceWeight_nonneg x n) (harman_correction_nonneg x n)
  · exact (Task379.referenceWeight_integral_pos (by linarith)).le

/-- A PNT error envelope with coefficient at most one is at least the reference length.
Derived quantitative diagnostic for the PNT invocation on MMS page 11.
This compares upper bound functions, not actual prime counting errors. -/
theorem pnt_envelope_ge_referenceLength {c x : ℝ} (hc : c ≤ 1) (hx : 1 ≤ x) :
    Task379.referenceLength x ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  unfold Task379.referenceLength
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply Real.exp_le_exp.mpr
  have hs := Real.sqrt_nonneg (Real.log x)
  nlinarith

/-- The same error envelope cannot fit even half the positive reference length.
Derived negative result for direct use of the lab StrongPNT on MMS page 11.
A stronger uniform input is required for the actual weighted rough number limits. -/
theorem pnt_envelope_not_half_referenceLength {c x : ℝ}
    (hc : c ≤ 1) (hx : 1 ≤ x) :
    ¬ x * Real.exp (-c * Real.sqrt (Real.log x)) ≤ Task379.referenceLength x / 2 := by
  have hh := Task379.referenceLength_pos (x := x) (by linarith)
  have he := pnt_envelope_ge_referenceLength hc hx
  linarith

/-- LEAF. The first rough indicator has limiting weighted coefficient four omega four.
MMS page 11 equation 5.1 and bottom Buchstab display.
This asks only for the first summand. The ordered triple sum is excluded.
The shrinking relative interval and the fixed smooth reference weight are explicit. -/
theorem roughReferenceMean_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |roughReferenceMean x - 4 * buchstabModel 4| ≤ δ := by
  sorry

/-- LEAF. The ordered triple correction has the displayed limiting Buchstab integral.
MMS page 11 equation 5.1 and bottom display, continued on page 12.
This excludes the first rough indicator, positivity and every numerical bound.
It requires the prime sum to integral passage uniformly over the ordered prime triples. -/
theorem correctionReferenceMean_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |correctionReferenceMean x - profileIntegral buchstabModel| ≤ δ := by
  sorry

/-- The exact sealed mean converges to the paper coefficient from the two smaller limits.
MMS page 11 bottom display. CONDITIONAL ON roughReferenceMean_limit
and correctionReferenceMean_limit. The tail bound is not used here. -/
theorem referenceMean_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |Task379.referenceMean x -
        (4 * buchstabModel 4 + profileIntegral buchstabModel)| ≤ δ := by
  intro δ hδ
  obtain ⟨X₁, h₁⟩ := roughReferenceMean_limit (δ / 2) (by linarith)
  obtain ⟨X₂, h₂⟩ := correctionReferenceMean_limit (δ / 2) (by linarith)
  refine ⟨max X₁ X₂, fun x hx => ?_⟩
  have hr := h₁ x ((le_max_left _ _).trans hx)
  have hc := h₂ x ((le_max_right _ _).trans hx)
  rw [referenceMean_split]
  have he : roughReferenceMean x + correctionReferenceMean x -
      (4 * buchstabModel 4 + profileIntegral buchstabModel) =
      (roughReferenceMean x - 4 * buchstabModel 4) +
        (correctionReferenceMean x - profileIntegral buchstabModel) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

/-- The sealed enveloped mean follows from three strictly smaller leaves.
MMS page 11 bottom display and page 12 first paragraph and footnote 3.
The local envelope and its integral unfold to the exact sealed formulas.
CONDITIONAL ON buchstabModel_tail, roughReferenceMean_limit
and correctionReferenceMean_limit. No numerical integral estimate is used. -/
theorem harman_reference_mean_enveloped_supply :
    ∃ αp : ℝ, 0 < αp ∧ αp ≤ 4 * referenceEnvelope 4 + profileIntegral referenceEnvelope ∧
      ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        |Task379.referenceMean x - αp| ≤ δ := by
  exact ⟨4 * buchstabModel 4 + profileIntegral buchstabModel,
    buchstab_coefficient_pos, buchstab_coefficient_le, referenceMean_limit⟩

end LeanLab.Ternary.MMS.Task571
