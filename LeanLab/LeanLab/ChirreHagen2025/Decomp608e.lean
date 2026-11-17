import Mathlib

/-!
Berndt 1972 page 153 displays 3.2 and 3.3, a polynomial proof of the derivative formula.
AI wrote this Lean code. Goldbach is open.
-/
open Polynomial
namespace LeanLab.ChirreHagen2025.Decomp608e

/-- Berndt page 153 display 3.3, signed first-kind Stirling coefficients. -/
noncomputable def signedFirst (k j : ℕ) : ℝ := (-1 : ℝ) ^ (k - j) * Nat.stirlingFirst k j

/-- Berndt page 153 display 3.3, the signed coefficient recurrence. -/
theorem signedFirst_succ_succ (k j : ℕ) :
    signedFirst (k + 1) (j + 1) = -(k : ℝ) * signedFirst k (j + 1) + signedFirst k j := by
  by_cases hj : j < k
  · unfold signedFirst
    rw [Nat.stirlingFirst_succ_succ]
    push_cast
    simp only [show k - j = (k - (j + 1)) + 1 by omega, pow_succ]
    ring
  · by_cases he : j = k
    · subst j
      simp [signedFirst, Nat.stirlingFirst_self,
        Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self k)]
    · have h1 : k < j := by omega
      simp [signedFirst, Nat.stirlingFirst_eq_zero_of_lt h1,
        Nat.stirlingFirst_eq_zero_of_lt (show k < j + 1 by omega),
        Nat.stirlingFirst_eq_zero_of_lt (show k + 1 < j + 1 by omega)]

/-- The auxiliary zero column for the recurrence in Berndt display 3.3. -/
theorem signedFirst_succ_zero (k : ℕ) : signedFirst (k + 1) 0 = 0 := by
  simp [signedFirst, Nat.stirlingFirst_succ_zero]

/-- Polynomial numerators of derivatives of the Berndt kernel, from display 3.2. -/
noncomputable def derivativePoly (n : ℕ) : ℕ → Polynomial ℝ
  | 0 => C ((n.factorial : ℝ)⁻¹) * X ^ n
  | k + 1 => (derivativePoly n k).derivative - C (k + 1 : ℝ) * derivativePoly n k

/-- Berndt displays 3.2 and 3.3, the exact polynomial coefficients. -/
theorem derivativePoly_coeff (n k j : ℕ) :
    (derivativePoly n k).coeff j =
      if j ≤ n then signedFirst (k + 1) (n + 1 - j) / j.factorial else 0 := by
  induction k generalizing j with
  | zero =>
    by_cases hj : j ≤ n
    · rw [ite_eq_left hj]
      by_cases he : j = n
      · subst j
        simp [derivativePoly, signedFirst, Nat.stirlingFirst_self]
      · have hnj : 1 < n + 1 - j := by omega
        simp [derivativePoly, signedFirst, coeff_X_pow, he,
          Nat.stirlingFirst_eq_zero_of_lt hnj ]
    · simp [derivativePoly, hj, coeff_X_pow, show j ≠ n by omega]
  | succ k ih =>
    simp only [derivativePoly, coeff_sub, coeff_derivative, coeff_C_mul]
    rw [ih (j + 1), ih j]
    by_cases hj : j < n
    · rw [ite_eq_left (by omega), ite_eq_left hj.le, ite_eq_left hj.le]
      simp only [show n + 1 - j = (n - j) + 1 by omega,
        show n + 1 - (j + 1) = n - j by omega,
        signedFirst_succ_succ (k + 1) (n - j), Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · by_cases he : j = n
      · subst j
        simp only [Nat.not_succ_le_self, ite_false, le_refl, ite_true, Nat.add_sub_cancel_left,
          zero_mul, Nat.sub_self]
        rw [signedFirst_succ_succ (k + 1) 0, signedFirst_succ_zero]
        push_cast
        ring
      · simp [show ¬j ≤ n by omega, show ¬j + 1 ≤ n by omega]

/-- The chain and quotient rules behind Berndt display 3.2. -/
theorem hasDerivAt_eval_log_div_pow (P : Polynomial ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => P.eval (Real.log y) / y ^ (k + 1))
      ((P.derivative - C (k + 1 : ℝ) * P).eval (Real.log x) / x ^ (k + 2)) x := by
  have hP := (P.hasDerivAt (Real.log x)).comp x (Real.hasDerivAt_log hx.ne')
  have h := hP.div (hasDerivAt_pow (k + 1) x) (pow_ne_zero _ hx.ne')
  convert h using 1
  · ext y
    rfl
  · simp only [Function.comp_apply, eval_sub, eval_mul, eval_C, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel_right, pow_succ]
    field_simp [hx.ne'] <;> ring

/-- Berndt display 3.2, repeated derivatives expressed by their numerator polynomial. -/
theorem iteratedDeriv_kernel_eq (n k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (fun y : ℝ => Real.log y ^ n / (y * (n.factorial : ℝ))) x =
      (derivativePoly n k).eval (Real.log x) / x ^ (k + 1) := by
  induction k generalizing x with
  | zero =>
    simp only [iteratedDeriv_zero, derivativePoly, eval_mul, eval_C, eval_pow, eval_X,
      Nat.zero_add, pow_one]
    ring
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k (fun y : ℝ => Real.log y ^ n / (y * (n.factorial : ℝ))) =ᶠ[
        nhds x] (fun y : ℝ => (derivativePoly n k).eval (Real.log y) / y ^ (k + 1)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact ih hy
    rw [heq.deriv_eq]
    exact (hasDerivAt_eval_log_div_pow (derivativePoly n k) k hx).deriv

/-- Berndt page 153 display 3.2, the exact normalized logarithmic derivative formula. -/
theorem iteratedDeriv_kernel_formula (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (fun y : ℝ => Real.log y ^ n / (y * (n.factorial : ℝ))) x =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j *
        ((Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) / j.factorial) *
        (Real.log x ^ j / x ^ (n + 1)) := by
  have hd : (derivativePoly n n).natDegree ≤ n := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [derivativePoly_coeff, ite_eq_right (by omega)]
  rw [iteratedDeriv_kernel_eq n n hx,
    eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
  rw [derivativePoly_coeff, ite_eq_left hjn, signedFirst,
    show n + 1 - (n + 1 - j) = j by omega]
  ring

end LeanLab.ChirreHagen2025.Decomp608e
