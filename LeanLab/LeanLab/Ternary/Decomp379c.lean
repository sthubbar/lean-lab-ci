/-
MMS https://arxiv.org/abs/1610.02017v2, pages 11 to 12.
Split the reference mean from the short interval Fourier transfer.
The explicit smooth profile is one permitted choice of the paper g1.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp361e

namespace LeanLab.Ternary.MMS.Task379
open Finset MeasureTheory
open scoped Interval

/-- The reference interval length h1 from MMS page 11 before Proposition 5.1. -/
noncomputable def referenceLength (x : ℝ) : ℝ :=
  x * Real.exp (-Real.sqrt (Real.log x))

/-- A fixed smooth profile rescaled to the paper long reference interval.
MMS page 11, the arbitrary smooth g1 in Proposition 5.1.
The Mathlib flat exponential factors give support in the closed interval
and strict positivity inside it. This particular profile is our choice. -/
noncomputable def referenceWeight (x t : ℝ) : ℝ :=
  expNegInvGlue ((t - x) / referenceLength x) *
    expNegInvGlue (1 - (t - x) / referenceLength x)

/-- The normalized reference mean, multiplied by log x.
MMS page 11 bottom display and page 12 definition of alpha plus.
The denominator is the zero frequency Fourier integral of g1.
For positive x the smooth weight has a positive integral. -/
noncomputable def referenceMean (x : ℝ) : ℝ :=
  Real.log x *
    (∑ n ∈ ints x (x + referenceLength x),
      referenceWeight x n * Task361.harmanMajorant x n) /
    (∫ t in x..(x + referenceLength x), referenceWeight x t)

/-- The chosen smooth reference profile is nonnegative.
Derived verification of the allowed g1 in MMS page 11 Proposition 5.1. -/
theorem referenceWeight_nonneg (x t : ℝ) : 0 ≤ referenceWeight x t := by
  exact mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

/-- The reference length is positive whenever x is positive.
MMS page 11 definition of h1. -/
theorem referenceLength_pos {x : ℝ} (hx : 0 < x) : 0 < referenceLength x :=
  mul_pos hx (Real.exp_pos _)

/-- The chosen g1 is strictly positive at the midpoint of its interval.
Derived nonvacuity check for MMS page 11 Proposition 5.1. -/
theorem referenceWeight_midpoint_pos {x : ℝ} (hx : 0 < x) :
    0 < referenceWeight x (x + referenceLength x / 2) := by
  have hh := referenceLength_pos hx
  have he : (x + referenceLength x / 2 - x) / referenceLength x = (1 / 2 : ℝ) := by
    field_simp [hh.ne']; ring
  unfold referenceWeight
  rw [he]
  exact mul_pos (expNegInvGlue.pos_of_pos (by norm_num))
    (expNegInvGlue.pos_of_pos (by norm_num))

/-- The chosen g1 is smooth of every finite order, including at its endpoints.
Derived verification of the allowed smooth reference profile in MMS page 11. -/
theorem referenceWeight_contDiff (x : ℝ) (k : ℕ) :
    ContDiff ℝ k (referenceWeight x) := by
  unfold referenceWeight
  exact (expNegInvGlue.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _)).mul
    (expNegInvGlue.contDiff.comp
      (contDiff_const.sub ((contDiff_id.sub contDiff_const).div_const _)))

/-- The reference weight is positive at every interior point.
Derived verification of the reference interval in MMS page 11. -/
theorem referenceWeight_pos_inside {x t : ℝ} (hx : 0 < x)
    (ht : x < t) (htu : t < x + referenceLength x) :
    0 < referenceWeight x t := by
  have hh := referenceLength_pos hx
  have hu : 0 < (t - x) / referenceLength x := div_pos (by linarith) hh
  have hv : (t - x) / referenceLength x < 1 :=
    (div_lt_one hh).mpr (by linarith)
  exact mul_pos (expNegInvGlue.pos_of_pos hu) (expNegInvGlue.pos_of_pos (by linarith))

/-- The reference weight vanishes off the interior of its prescribed interval.
Derived support verification for MMS page 11 Proposition 5.1. -/
theorem referenceWeight_zero_outside {x t : ℝ} (hx : 0 < x)
    (ht : t ≤ x ∨ x + referenceLength x ≤ t) : referenceWeight x t = 0 := by
  have hh := referenceLength_pos hx
  unfold referenceWeight
  rcases ht with ht | ht
  · rw [expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le),
      zero_mul]
  · have hu : 1 ≤ (t - x) / referenceLength x :=
      (one_le_div hh).mpr (by linarith)
    rw [expNegInvGlue.zero_of_nonpos (by linarith : 1 - (t - x) / referenceLength x ≤ 0),
      mul_zero]

/-- The normalization denominator is strictly positive for every positive x.
Derived nonvacuity verification for the reference mean on MMS page 11. -/
theorem referenceWeight_integral_pos {x : ℝ} (hx : 0 < x) :
    0 < ∫ t in x..(x + referenceLength x), referenceWeight x t := by
  have hh := referenceLength_pos hx
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((referenceWeight_contDiff x 0).continuous.intervalIntegrable _ _)
  · intro t ht
    exact referenceWeight_pos_inside hx ht.1 ht.2
  · linarith

/-- The normalized reference mean is nonnegative once x is at least one.
Derived sign verification of the mean in MMS page 11 bottom display. -/
theorem referenceMean_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ referenceMean x := by
  have hx0 : 0 < x := by linarith
  unfold referenceMean
  apply div_nonneg
  · apply mul_nonneg (Real.log_nonneg hx)
    apply sum_nonneg
    intro n hn
    exact mul_nonneg (referenceWeight_nonneg x n) (Task361.harmanMajorant_nonneg x n)
  · exact (referenceWeight_integral_pos hx0).le

/-- LEAF. The long interval mean has a fixed density below 2.9.
MMS page 11 bottom Buchstab integral display and page 12 first paragraph.
The proof uses the prime number theorem and the triple Buchstab integral.
The density is fixed before the tolerance and before x. -/
theorem harman_reference_mean :
    ∃ αp : ℝ, 0 < αp ∧ αp < 2.9 ∧
      ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        |referenceMean x - αp| ≤ δ := by sorry

/-- LEAF. The reference mean transfers to the short interval Fourier condition.
MMS page 11 Proposition 5.1, page 12 unsmoothing displays, and its proofs
in sections 5.1 to 5.3, pages 13 to 27.
Only the limiting mean is assumed. Its evaluation and its numerical bound
are excluded from this leaf. The paper explicitly permits the lopsided interval. -/
theorem harman_fourier_of_reference_mean (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
    (αp : ℝ)
    (hmean : ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |referenceMean x - αp| ≤ δ) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Hyp1 θ x αp η (Task361.harmanMajorant x) := by sorry

/-- The exact explicit majorant Fourier input from its two smaller components.
MMS pages 11 and 12. CONDITIONAL ON harman_reference_mean and
harman_fourier_of_reference_mean. -/
theorem harman_fourier_input_decomposed (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ αp : ℝ, 0 < αp ∧ αp < 2.9 ∧
      ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        Hyp1 θ x αp η (Task361.harmanMajorant x) := by
  obtain ⟨αp, hp, hp29, hmean⟩ := harman_reference_mean
  exact ⟨αp, hp, hp29, harman_fourier_of_reference_mean θ hθ hθ1 αp hmean⟩

end LeanLab.Ternary.MMS.Task379
