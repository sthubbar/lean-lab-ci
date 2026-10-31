/-
P0059 arXiv 1407.7902v1 page 9 equation 3.2, in squared norm form.
Journal INTEGERS 14 A61 page 12 equation 66.
AI wrote this Lean code, CODEX task64, 2026-10-25.
-/
import LeanLab.KadiriLumley2014.PolynomialParts

namespace LeanLab.KadiriLumley2014.Task64
open Real Set MeasureTheory intervalIntegral Polynomial

/-- The top derivative of a polynomial with the given degree bound is constant. -/
theorem polynomial_top_derivative (p : ℝ[X]) (d : ℕ) (hd : p.natDegree ≤ d) :
    Polynomial.derivative^[d] p = C ((d.factorial : ℝ) * p.coeff d) := by
  ext j
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hj : j = 0
  · subst j
    simp [Nat.descFactorial_self]
  · have hc : p.coeff (j + d) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hc, hj]

/-- Degree and leading coefficient of the unscaled polynomial weight. -/
theorem unitWeightPoly_degree (m : ℕ) :
    (unitWeightPoly m).natDegree = 2 * m ∧ (unitWeightPoly m).coeff (2 * m) = (-1 : ℝ) ^ m := by
  have hs : (1 - (X : ℝ[X])).natDegree = 1 := by
    simpa using Polynomial.natDegree_sub_eq_right_of_natDegree_lt
      (p := (1 : ℝ[X])) (q := X) (by simp)
  have hn : (1 - (X : ℝ[X])) ≠ 0 := by
    intro hz
    rw [hz] at hs
    simp at hs
  have hd : (unitWeightPoly m).natDegree = 2 * m := by
    unfold unitWeightPoly
    rw [Polynomial.natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hn)]
    simp [hs, Polynomial.natDegree_pow]
    omega
  have hl : (1 - (X : ℝ[X])).leadingCoeff = -1 := by
    simpa using Polynomial.leadingCoeff_sub_of_degree_lt'
      (p := (1 : ℝ[X])) (q := X) (by simp)
  refine ⟨hd, ?_⟩
  rw [← hd, Polynomial.coeff_natDegree]
  simp [unitWeightPoly, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow, hl]

/-- Squared m-th derivative mass of the unscaled beta polynomial. -/
theorem unitWeightPoly_derivative_sq_integral (m : ℕ) :
    (∫ t in (0 : ℝ)..1, ((Polynomial.derivative^[m] (unitWeightPoly m)).eval t) ^ 2) =
      (m.factorial : ℝ) ^ 2 / (2 * m + 1) := by
  have hp := polynomial_parts m (unitWeightPoly m) (Polynomial.derivative^[m] (unitWeightPoly m))
    (fun k hk => unitWeightPoly_zero hk) (fun k hk => unitWeightPoly_one hk)
  have hiter : Polynomial.derivative^[m] (Polynomial.derivative^[m] (unitWeightPoly m)) =
      Polynomial.derivative^[2 * m] (unitWeightPoly m) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have htop := polynomial_top_derivative (unitWeightPoly m) (2 * m) (unitWeightPoly_degree m).1.le
  rw [(unitWeightPoly_degree m).2] at htop
  rw [hiter, htop] at hp
  simp only [Polynomial.eval_C] at hp
  rw [intervalIntegral.integral_mul_const] at hp
  have hmass : (∫ t in (0 : ℝ)..1, (unitWeightPoly m).eval t) =
      (m.factorial : ℝ) ^ 2 / (2 * m + 1).factorial := by
    simp only [unitWeightPoly, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
    rw [integral_nat_beta]
    have hi : m + m + 1 = 2 * m + 1 := by omega
    rw [hi]
    ring
  rw [hmass] at hp
  have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  have hf : ((2 * m).factorial : ℝ) ≠ 0 := by positivity
  have hf' : ((2 * m + 1).factorial : ℝ) = (2 * m + 1) * (2 * m).factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  simp_rw [← sq] at hp
  rw [hp, hf']
  field_simp
  nlinarith [hsign]

/-- The squared L2 norm of the m-th derivative of the paper's weight. -/
theorem weight_mth_derivative_sq_integral (m : ℕ) :
    (∫ t in (0 : ℝ)..1, (iteratedDeriv m (weight m) t) ^ 2) =
      (2 ^ (2 * m) * (m.factorial : ℝ)) ^ 2 / (2 * m + 1) := by
  have heq : weight m = fun t : ℝ => (C ((4 : ℝ) ^ m) * unitWeightPoly m).eval t := by
    funext t
    simp only [weight, unitWeightPoly, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one, mul_pow]
    ring
  rw [heq, iteratedDeriv_eval, Polynomial.iterate_derivative_C_mul]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul, unitWeightPoly_derivative_sq_integral]
  have hpow : (4 : ℝ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  rw [hpow]
  ring

end LeanLab.KadiriLumley2014.Task64
