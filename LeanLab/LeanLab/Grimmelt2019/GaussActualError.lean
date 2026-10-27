/-
AI wrote this Lean code for CODEX task51.
P0074 page 9, the main term and actual error after equation 27.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.GaussError

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual sequence error is exactly the Gauss-weighted centered character error. -/
theorem gauss_actual_error_eq {q : ℕ} [NeZero q] (W : Finset ℤ) (ν : ℤ → ℝ)
    (r : ℤ) (hr : Int.gcd r q = 1) (M : ℝ)
    (hs : ∀ n ∈ W, ν n ≠ 0 → Int.gcd n q = 1) :
    (∑ n ∈ W, (ν n : ℂ) * LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / q)) -
        (ArithmeticFunction.moebius q : ℂ) * M / q.totient =
      gaussError Finset.univ (r : ZMod q) (fun χ =>
        (∑ n ∈ W, (ν n : ℂ) * χ (n : ZMod q)) - if χ = 1 then (M : ℂ) else 0) := by
  have hu : IsUnit (r : ZMod q) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm, Int.isCoprime_iff_gcd_eq_one]
    exact hr
  have hmain : (∑ χ : DirichletCharacter ℂ q,
      (gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q)) *
        (if χ = 1 then (M : ℂ) else 0)) =
      (ArithmeticFunction.moebius q : ℂ) * M := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      inv_one, gaussSum_principal, MulChar.one_apply hu, mul_one]
  rw [gauss_weighted_expansion W ν r hr hs]
  unfold gaussError
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hmain]
  ring

/-- The actual squared exponential error is bounded by q over totient times the character error energy. -/
theorem gauss_actual_error_sq_le {q : ℕ} [NeZero q] (W : Finset ℤ) (ν : ℤ → ℝ)
    (r : ℤ) (hr : Int.gcd r q = 1) (M : ℝ)
    (hs : ∀ n ∈ W, ν n ≠ 0 → Int.gcd n q = 1) :
    ‖(∑ n ∈ W, (ν n : ℂ) * LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / q)) -
        (ArithmeticFunction.moebius q : ℂ) * M / q.totient‖ ^ 2 ≤
      (q : ℝ) / q.totient * ∑ χ : DirichletCharacter ℂ q,
        ‖(∑ n ∈ W, (ν n : ℂ) * χ (n : ZMod q)) - if χ = 1 then (M : ℂ) else 0‖ ^ 2 := by
  rw [gauss_actual_error_eq W ν r hr M hs]
  exact gaussError_univ_sq_le _ _

/-- The exceptional and nonexceptional pieces control the actual error with their own counts. -/
theorem gauss_actual_error_split_sq_le {q : ℕ} [NeZero q] (W : Finset ℤ) (ν : ℤ → ℝ)
    (r : ℤ) (hr : Int.gcd r q = 1) (M : ℝ)
    (hs : ∀ n ∈ W, ν n ≠ 0 → Int.gcd n q = 1)
    (A : Finset (DirichletCharacter ℂ q)) :
    ‖(∑ n ∈ W, (ν n : ℂ) * LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / q)) -
        (ArithmeticFunction.moebius q : ℂ) * M / q.totient‖ ^ 2 ≤
      2 * ((q : ℝ) * A.card / (q.totient : ℝ) ^ 2 * ∑ χ ∈ A,
        ‖(∑ n ∈ W, (ν n : ℂ) * χ (n : ZMod q)) - if χ = 1 then (M : ℂ) else 0‖ ^ 2) +
      2 * ((q : ℝ) * (Finset.univ \ A).card / (q.totient : ℝ) ^ 2 * ∑ χ ∈ Finset.univ \ A,
        ‖(∑ n ∈ W, (ν n : ℂ) * χ (n : ZMod q)) - if χ = 1 then (M : ℂ) else 0‖ ^ 2) := by
  rw [gauss_actual_error_eq W ν r hr M hs]
  apply (gaussError_split_sq_le A _ _).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (gaussError_sq_le A _ _) (by norm_num))
    (mul_le_mul_of_nonneg_left (gaussError_sq_le (Finset.univ \ A) _ _) (by norm_num))

#print axioms gauss_actual_error_eq
#print axioms gauss_actual_error_sq_le
#print axioms gauss_actual_error_split_sq_le
end LeanLab.Grimmelt2019.MainTerm
