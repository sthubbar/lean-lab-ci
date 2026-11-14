/-
Jia 1996 pages 261 to 262 and 283 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
Argument ranges for the global Buchstab bounds used in Lemma 28.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Languasco2004.Geometry565
open Real intervalIntegral
noncomputable section

/-- Page 283 display 60: the pair integral uses the global lower bound from argument four. -/
theorem main1_argument (t u : ℝ) (ht : t ≤ 89 / 462) (hu : u ≤ t) :
    (4 : ℝ) ≤ 135 / 16 * (1 - t - u) := by
  linarith

/-- Page 285 remaining pair integral: its argument is also at least four. -/
theorem mainRest_argument (t u : ℝ) (ht : t ≤ 17 / 54)
    (hu : u ≤ 89 / 288 - 29 / 48 * t) :
    (4 : ℝ) ≤ 135 / 16 * (1 - t - u) := by
  linarith

/-- Pages 284 and 285: below the middle boundary, the triple argument is at least four. -/
theorem triple_four_argument (t u v : ℝ) (hu : t + 2 * u ≤ 71 / 135) (hv : v ≤ u) :
    (4 : ℝ) ≤ 135 / 16 * (1 - t - u - v) := by
  linarith

/-- Page 285 before display 64: the upper triangular triple region uses argument at least three. -/
theorem triple_three_region1_argument (t u v : ℝ) (ht : t ≤ 89 / 462)
    (hu : u ≤ t) (hv : v ≤ u) :
    (3 : ℝ) ≤ 135 / 16 * (1 - t - u - v) := by
  linarith

/-- Page 285 remaining triple integrals: the sloping upper boundary gives argument at least three. -/
theorem triple_three_remainder_argument (t u v : ℝ) (ht : 89 / 462 ≤ t)
    (hu : u ≤ 89 / 288 - 29 / 48 * t) (hv : v ≤ u) :
    (3 : ℝ) ≤ 135 / 16 * (1 - t - u - v) := by
  linarith

/-- Pages 284 and 285: the middle boundary lies between the cutoff and t on its source interval. -/
theorem middle_boundary_domain (t : ℝ) (htL : 71 / 405 ≤ t) (htU : t ≤ 13 / 45) :
    (16 / 135 : ℝ) ≤ (71 / 135 - t) / 2 ∧ (71 / 135 - t) / 2 ≤ t := by
  constructor <;> linarith

/-- Page 285: the remaining pair boundary lies between the cutoff and t on its full source interval. -/
theorem remaining_boundary_domain (t : ℝ) (htL : 89 / 462 ≤ t) (htU : t ≤ 17 / 54) :
    (16 / 135 : ℝ) ≤ 89 / 288 - 29 / 48 * t ∧ 89 / 288 - 29 / 48 * t ≤ t := by
  constructor <;> linarith

/-- Pages 261 and 262 display 41: a weighted integral recurrence propagates local bounds.
CONDITIONAL ON the displayed recurrence and the bounds on the preceding strip.
This proves the elementary induction step, not the source numerical base bounds. -/
theorem buchstab_strip_from_recurrence (w : ℝ → ℝ) (K u l U : ℝ)
    (hK : 0 < K) (hKu : K ≤ u) (hwK : l ≤ w K ∧ w K ≤ U)
    (hi : IntervalIntegrable w MeasureTheory.volume (K - 1) (u - 1))
    (hb : ∀ t ∈ Set.Icc (K - 1) (u - 1), l ≤ w t ∧ w t ≤ U)
    (hrec : u * w u = K * w K + ∫ t in (K - 1)..(u - 1), w t) :
    l ≤ w u ∧ w u ≤ U := by
  have hab : K - 1 ≤ u - 1 := by linarith
  have hL := integral_mono_on hab (intervalIntegrable_const (c := l)) hi
    (fun t ht => (hb t ht).1)
  have hU := integral_mono_on hab hi (intervalIntegrable_const (c := U))
    (fun t ht => (hb t ht).2)
  simp only [integral_const, smul_eq_mul] at hL hU
  have hKL := mul_le_mul_of_nonneg_left hwK.1 hK.le
  have hKU := mul_le_mul_of_nonneg_left hwK.2 hK.le
  constructor <;> nlinarith

/-- Pages 283 to 285: concrete interior points satisfy the source argument premises. -/
theorem argument_domain_instances :
    (16 / 135 : ℝ) < 1 / 6 ∧ (1 / 6 : ℝ) < 89 / 462 ∧
    (16 / 135 : ℝ) < 1 / 7 ∧ (1 / 7 : ℝ) < 1 / 6 ∧
    (89 / 462 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < 17 / 54 ∧
    (16 / 135 : ℝ) < 3 / 20 ∧ (3 / 20 : ℝ) < 89 / 288 - 29 / 48 * (1 / 4) := by
  norm_num

#print axioms main1_argument
#print axioms mainRest_argument
#print axioms triple_four_argument
#print axioms triple_three_region1_argument
#print axioms triple_three_remainder_argument
#print axioms middle_boundary_domain
#print axioms remaining_boundary_domain
#print axioms buchstab_strip_from_recurrence
#print axioms argument_domain_instances
end
end LeanLab.Languasco2004.Geometry565
