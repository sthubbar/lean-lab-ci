/-
P0059 arXiv 1407.7902v1 page 10, Rodrigues formula after Lemma 3.1.
Journal INTEGERS 14 A61 page 13.
The sign comparison is recorded only as a QUESTION in the ledgers.
AI wrote this Lean code, CODEX task64, 2026-10-25.
-/
import LeanLab.KadiriLumley2014.PolynomialParts

namespace LeanLab.KadiriLumley2014.Task64
open Real Polynomial

/-- The shifted Legendre polynomial with the standard Rodrigues sign. -/
noncomputable def shiftedLegendreValue (m : ℕ) (t : ℝ) : ℝ :=
  ((Polynomial.shiftedLegendre m).map (Int.castRingHom ℝ)).eval t

/-- Rodrigues formula for the unscaled weight. -/
theorem unitWeight_rodrigues (m : ℕ) (t : ℝ) :
    (Polynomial.derivative^[m] (unitWeightPoly m)).eval t =
      (m.factorial : ℝ) * shiftedLegendreValue m t := by
  have h := congrArg (fun p : ℤ[X] => (p.map (Int.castRingHom ℝ)).eval t)
    (Polynomial.factorial_mul_shiftedLegendre_eq m)
  rw [← Polynomial.iterate_derivative_map] at h
  simpa [unitWeightPoly, shiftedLegendreValue] using h.symm

/-- Rodrigues formula for the actual polynomial weight. -/
theorem weight_rodrigues (m : ℕ) (t : ℝ) :
    iteratedDeriv m (weight m) t = (4 : ℝ) ^ m * m.factorial * shiftedLegendreValue m t := by
  have heq : weight m = fun t : ℝ => (4 : ℝ) ^ m * (unitWeightPoly m).eval t := by
    funext t
    simp only [weight, unitWeightPoly, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one, mul_pow]
    ring
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_eval]
  change (4 : ℝ) ^ m * (Polynomial.derivative^[m] (unitWeightPoly m)).eval t = _
  rw [unitWeight_rodrigues]
  ring

/-- The standard shifted polynomial has value one at zero. -/
theorem shiftedLegendreValue_zero (m : ℕ) : shiftedLegendreValue m 0 = 1 := by
  unfold shiftedLegendreValue
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
  norm_num

/-- Literal binomial expression printed after the Rodrigues identity. -/
noncomputable def printedShiftedExpression (m : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1),
    (m.choose k : ℝ) * (m + k).choose k * (-t) ^ k

/-- The printed expression has value minus one at zero for odd m. -/
theorem printedShiftedExpression_zero (m : ℕ) :
    printedShiftedExpression m 0 = (-1 : ℝ) ^ m := by
  unfold printedShiftedExpression
  have hs : (∑ k ∈ Finset.range (m + 1),
      (m.choose k : ℝ) * (m + k).choose k * (-(0 : ℝ)) ^ k) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      simp [zero_pow hk0]
    · simp
  rw [hs, mul_one]

/-- At m = 3 the two literal identities on the page have opposite signs.
This is a local identity check, not a claim that Theorem 1.1 fails. -/
theorem printed_rodrigues_sign_at_three :
    iteratedDeriv 3 (weight 3) (1 / 4) = -168 ∧
    (4 : ℝ) ^ 3 * (3 : ℕ).factorial * printedShiftedExpression 3 (1 / 4) = 168 := by
  rw [weight_rodrigues]
  norm_num [shiftedLegendreValue, Polynomial.shiftedLegendre, printedShiftedExpression,
    Finset.sum_range_succ, Nat.choose]

/-- A global sign change preserves the absolute values used for the norm. -/
theorem abs_sign_invariant (m : ℕ) (x : ℝ) : |(-1 : ℝ) ^ m * x| = |x| := by
  simp [abs_mul]

end LeanLab.KadiriLumley2014.Task64
