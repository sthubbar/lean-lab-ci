/-
A record about the split SPLIT_near_sup357_local_variation357: its second leaf
near_sup357_integral_norm_sq357, the Cauchy and Schwarz inequality for an interval
integral stated for every complex valued function with no integrability hypothesis,
is false as stated. The witness is the function beta to the power minus one half on
the interval from zero to one. It is integrable there with integral 2, so the left
side is 4. Its squared norm is one over beta, which is not integrable on that
interval, so the Lean interval integral on the right side is zero by convention.
The inequality would then read 4 at most 0. The statement below is the universal
closure of the leaf, character for character in its body. The inequality is the
standard one once the squared norm is assumed integrable; P0093 page 158 uses it
only for a continuous integrand. AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Linnik1951

open MeasureTheory

/-- On the nonnegative reals the squared norm of beta to the power minus one half,
read as a complex number, is one over beta. At zero both sides are zero by the Lean
conventions for a negative power of zero and for the inverse of zero. -/
theorem norm_sq_rpow_neg_half357 {β : ℝ} (hβ : 0 ≤ β) :
    ‖((β ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)‖ ^ 2 = β⁻¹ := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Real.rpow_natCast,
    ← Real.rpow_mul hβ, ← Real.rpow_neg_one]
  norm_num

/-- The interval integral from zero to one of beta to the power minus one half, read
as a complex number, is 2. -/
theorem integral_rpow_neg_half357 :
    ∫ β in (0 : ℝ)..1, ((β ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) = 2 := by
  rw [intervalIntegral.integral_ofReal, integral_rpow (Or.inl (by norm_num))]
  norm_num

/-- The interval integral from zero to one of the squared norm of beta to the power
minus one half is zero in Lean, because one over beta is not interval integrable
across zero and the integral of a non integrable function is zero by convention. -/
theorem integral_norm_sq_rpow_neg_half357 :
    ∫ β in (0 : ℝ)..1, ‖((β ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)‖ ^ 2 = 0 := by
  have hcongr : ∫ β in (0 : ℝ)..1, ‖((β ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)‖ ^ 2 =
      ∫ β in (0 : ℝ)..1, β⁻¹ := by
    refine intervalIntegral.integral_congr (fun β hβ => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hβ
    exact norm_sq_rpow_neg_half357 hβ.1
  rw [hcongr]
  refine intervalIntegral.integral_undef (fun h => ?_)
  rcases intervalIntegrable_inv_iff.mp h with h01 | h0
  · exact zero_ne_one h01
  · exact h0 (Set.left_mem_uIcc)

/-- FALSE: the universal closure of the leaf near_sup357_integral_norm_sq357 of
SPLIT_near_sup357_local_variation357 fails. With g equal to beta to the power minus
one half and alpha equal to one, the left side is 4 and the right side is 0. So that
leaf cannot be proved as stated; it needs a hypothesis such as interval integrability
of the squared norm of g, which holds in its one use, where g is continuous. -/
theorem near_sup357_integral_norm_sq357_false :
    ¬ (∀ (g : ℝ → ℂ) {α : ℝ} (_ : 0 ≤ α),
      ‖∫ β in (0 : ℝ)..α, g β‖ ^ 2 ≤ α * ∫ β in (0 : ℝ)..α, ‖g β‖ ^ 2) := by
  intro h
  have h1 := h (fun β : ℝ => ((β ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)) (α := 1) zero_le_one
  rw [integral_rpow_neg_half357, integral_norm_sq_rpow_neg_half357] at h1
  norm_num at h1

end LeanLab.Linnik1951
