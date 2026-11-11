import LeanLab.HelfgottMajor.Decomp457b

/-!
Splitting the numerical square energy budget of `Decomp457b.principal_log_weight_budget`
into two smaller steps.

The bound is the size of the square energy of the logarithmic derivative weight on the
left contour, the norm of `logDeriv riemannZeta` at `-1/2 + it` divided by the norm of
`-1/2 + it`. The split cuts the vertical line at height two and bounds the two pieces of
the energy separately:

* the short range `|t| ≤ 2`, where the weight is largest but the interval is short,
* the long range `2 < |t|`, where only the decay of the weight is paid for.

The two bounds add up to 210, and `210 ≤ (6.01 * sqrt (2 * pi)) ^ 2` because
`2 * pi > 6`, so the square root bound of the split theorem follows by monotonicity of
the square root. No prime sum, no zero sum and no scale appears in either step.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457

/-- LEAF. The short range step: the square energy of the logarithmic derivative weight
over `|t| ≤ 2` is at most twenty. This is the piece where the weight is largest and the
interval is short, and it carries the whole numerical size of the small range. -/
theorem principal_log_weight_sq_short :
    (∫ t in {t : ℝ | |t| ≤ 2}, ‖principalLogWeight t‖ ^ 2) ≤ 20 := by
  sorry

/-- LEAF. The long range step: the square energy of the logarithmic derivative weight
over `2 < |t|` is at most one hundred and ninety. This is the decay step, where the
weight falls off and only the length of the two half lines is paid for. -/
theorem principal_log_weight_sq_long :
    (∫ t in {t : ℝ | 2 < |t|}, ‖principalLogWeight t‖ ^ 2) ≤ 190 := by
  sorry

/-- The square energy budget, assembled from the two range bounds. The line is cut at
height two, the two pieces add to the whole energy, and the total 210 is below
`(6.01 * sqrt (2 * pi)) ^ 2 = 6.01 ^ 2 * (2 * pi) > 6.01 ^ 2 * 6`. -/
theorem principal_log_weight_budget_split :
    sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) ≤ 6.01 * sqrt (2 * π) := by
  classical
  have hset : ({t : ℝ | |t| ≤ 2} : Set ℝ) = Set.Icc (-2) 2 := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  have hmeas : MeasurableSet ({t : ℝ | |t| ≤ 2} : Set ℝ) := by
    rw [hset]
    exact measurableSet_Icc
  have hcompl : ({t : ℝ | |t| ≤ 2} : Set ℝ)ᶜ = {t : ℝ | 2 < |t|} := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, abs_le, not_and_or, not_le, lt_abs]
    constructor
    · rintro (h | h)
      · right; linarith
      · left; linarith
    · rintro (h | h)
      · right; linarith
      · left; linarith
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  have hsplit := integral_add_compl (f := fun t : ℝ => ‖principalLogWeight t‖ ^ 2) hmeas hint
  have htotal : (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) ≤ 210 := by
    rw [← hsplit, hcompl]
    linarith [principal_log_weight_sq_short, principal_log_weight_sq_long]
  have hsq : (6.01 * sqrt (2 * π)) ^ 2 = 6.01 ^ 2 * (2 * π) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsix : (6 : ℝ) < 2 * π := by
    have h := Real.pi_gt_three
    linarith
  have hbig : (210 : ℝ) ≤ (6.01 * sqrt (2 * π)) ^ 2 := by
    have h601 : (6.01 : ℝ) ^ 2 = 36.1201 := by norm_num
    rw [hsq, h601]
    nlinarith [hsix]
  calc sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2)
      ≤ sqrt ((6.01 * sqrt (2 * π)) ^ 2) := Real.sqrt_le_sqrt (le_trans htotal hbig)
    _ = 6.01 * sqrt (2 * π) := Real.sqrt_sq (by positivity)

end LeanLab.HelfgottMajor.Decomp457b

#print axioms LeanLab.HelfgottMajor.Decomp457b.principal_log_weight_budget_split
