/-
P0087 Akeno 2026 page 5, coefficients in the Vaughan decomposition.
Elementary coefficient bounds do not yet prove the required subpolynomial divisor bound.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.Vaughan86

namespace LeanLab.Akeno2026.VaughanCoeffs86
open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open LeanLab.Akeno2026.Vaughan86
/-- LEAF. Page 5, the long Mobius convolution coefficient is bounded by the divisor count. -/
theorem long_mu_zeta_bound (U : ℝ) (n : ℕ) :
    |(((moebius : ArithmeticFunction ℝ) - shortPart (moebius : ArithmeticFunction ℝ) U) *
      (zeta : ArithmeticFunction ℝ)) n| ≤ (n.divisors.card : ℝ) := by
  rw [coe_mul_zeta_apply]
  calc
    _ ≤ ∑ d ∈ n.divisors,
        |((moebius : ArithmeticFunction ℝ) - shortPart (moebius : ArithmeticFunction ℝ) U) d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      change |(moebius d : ℝ) - (if (d : ℝ) ≤ U then (moebius d : ℝ) else 0)| ≤ 1
      by_cases hh : (d : ℝ) ≤ U
      · simp [hh]
      · simp only [hh, ite_false, sub_zero]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ = _ := by simp
/-- LEAF. Page 5, the long Mobius convolution coefficient vanishes below its cutoff. -/
theorem long_mu_zeta_support (U : ℝ) {n : ℕ} (hn : (n : ℝ) ≤ U) :
    (((moebius : ArithmeticFunction ℝ) - shortPart (moebius : ArithmeticFunction ℝ) U) *
      (zeta : ArithmeticFunction ℝ)) n = 0 := by
  by_cases hn0 : n = 0
  · simp [hn0]
  rw [coe_mul_zeta_apply]
  apply sum_eq_zero
  intro d hd
  have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hd)
  have hdU : (d : ℝ) ≤ U := (Nat.cast_le.mpr hdn).trans hn
  change (moebius d : ℝ) - (if (d : ℝ) ≤ U then (moebius d : ℝ) else 0) = 0
  simp [hdU]
/-- LEAF. Page 5 coefficient estimates, a linear bound alone is too weak for arbitrary powers. -/
theorem linear_bound_not_subpolynomial (C : ℝ) (hC : 0 ≤ C) :
    ∃ X : ℝ, 1 ≤ X ∧ C * X ^ ((1 : ℝ) / 2) < X := by
  refine ⟨(C + 1) ^ 2, by nlinarith, ?_⟩
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  nlinarith

/-- LEAF. Page 5, the short Mobius and short von Mangoldt convolution is bounded by log n. -/
theorem short_mu_lambda_bound (U V : ℝ) (n : ℕ) :
    |(shortPart (moebius : ArithmeticFunction ℝ) U * shortPart vonMangoldt V) n| ≤
      Real.log n := by
  calc
    _ = |∑ x ∈ n.divisorsAntidiagonal,
      shortPart (moebius : ArithmeticFunction ℝ) U x.1 * shortPart vonMangoldt V x.2| := by
        rw [ArithmeticFunction.mul_apply]
    _ ≤ ∑ x ∈ n.divisorsAntidiagonal,
      |shortPart (moebius : ArithmeticFunction ℝ) U x.1 * shortPart vonMangoldt V x.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ n.divisorsAntidiagonal, (zeta : ArithmeticFunction ℝ) x.1 * vonMangoldt x.2 := by
      apply sum_le_sum
      intro x hx
      have hz : (zeta : ArithmeticFunction ℝ) x.1 = 1 := by
        rw [ArithmeticFunction.natCoe_apply,
          ArithmeticFunction.zeta_apply_ne (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx), Nat.cast_one]
      have hmu : |shortPart (moebius : ArithmeticFunction ℝ) U x.1| ≤ 1 := by
        by_cases hh : (x.1 : ℝ) ≤ U
        · simpa [shortPart, hh] using
            (show |(moebius x.1 : ℝ)| ≤ 1 by exact_mod_cast
              (ArithmeticFunction.abs_moebius_le_one (n := x.1)))
        · simp [shortPart, hh]
      have hlam : |shortPart vonMangoldt V x.2| ≤ vonMangoldt x.2 := by
        by_cases hh : (x.2 : ℝ) ≤ V
        · simp [shortPart, hh, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        · simp [shortPart, hh]
      rw [abs_mul, hz, one_mul]
      exact (mul_le_mul hmu hlam (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = ((zeta : ArithmeticFunction ℝ) * vonMangoldt) n := ArithmeticFunction.mul_apply.symm
    _ = Real.log n := by rw [ArithmeticFunction.zeta_mul_vonMangoldt]; rfl

/-- LEAF. Page 5, the elementary linear majorant for the long Mobius coefficient. -/
theorem long_mu_zeta_linear_bound (U : ℝ) (n : ℕ) :
    |(((moebius : ArithmeticFunction ℝ) - shortPart (moebius : ArithmeticFunction ℝ) U) *
      (zeta : ArithmeticFunction ℝ)) n| ≤ (n : ℝ) := by
  exact (long_mu_zeta_bound U n).trans (Nat.cast_le.mpr (Nat.card_divisors_le_self n))

end LeanLab.Akeno2026.VaughanCoeffs86
