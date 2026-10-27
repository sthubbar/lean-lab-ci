/-
AI wrote this Lean code for CODEX task51.
P0074 page 10, the averaged Gauss-error step of Lemma 3.3.
The local analytic character energy estimate remains an explicit input.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.GaussActualError

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite summation of the subset Cauchy bound preserves the exact character count. -/
theorem gaussError_energy_le {q : ℕ} [NeZero q] {ι : Type*} (T : Finset ι)
    (A : Finset (DirichletCharacter ℂ q)) (r : ZMod q)
    (D : ι → DirichletCharacter ℂ q → ℂ) :
    (∑ t ∈ T, ‖gaussError A r (D t)‖ ^ 2) ≤
      ((q : ℝ) * A.card / (q.totient : ℝ) ^ 2) *
        ∑ χ ∈ A, ∑ t ∈ T, ‖D t χ‖ ^ 2 := by
  calc
    _ ≤ ∑ t ∈ T, ((q : ℝ) * A.card / (q.totient : ℝ) ^ 2) *
        ∑ χ ∈ A, ‖D t χ‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact gaussError_sq_le A r (D t)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

/-- An explicit character-energy budget gives the corresponding Gauss-error energy budget. -/
theorem gaussError_energy_of_bound {q : ℕ} [NeZero q] {ι : Type*} (T : Finset ι)
    (A : Finset (DirichletCharacter ℂ q)) (r : ZMod q)
    (D : ι → DirichletCharacter ℂ q → ℂ) (K : ℝ)
    (henergy : ∑ χ ∈ A, ∑ t ∈ T, ‖D t χ‖ ^ 2 ≤ K) :
    (∑ t ∈ T, ‖gaussError A r (D t)‖ ^ 2) ≤
      ((q : ℝ) * A.card / (q.totient : ℝ) ^ 2) * K := by
  exact (gaussError_energy_le T A r D).trans
    (mul_le_mul_of_nonneg_left henergy (by positivity))

/-- The actual sequence error energy is controlled by the centered character energy. -/
theorem gauss_actual_error_energy_le {q : ℕ} [NeZero q] (T : Finset ℤ)
    (W : ℤ → Finset ℤ) (ν : ℤ → ℝ) (r : ℤ) (hr : Int.gcd r q = 1) (M : ℤ → ℝ)
    (hs : ∀ t ∈ T, ∀ n ∈ W t, ν n ≠ 0 → Int.gcd n q = 1) :
    (∑ t ∈ T, ‖(∑ n ∈ W t, (ν n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / q)) -
        (ArithmeticFunction.moebius q : ℂ) * M t / q.totient‖ ^ 2) ≤
      (q : ℝ) / q.totient * ∑ χ : DirichletCharacter ℂ q, ∑ t ∈ T,
        ‖(∑ n ∈ W t, (ν n : ℂ) * χ (n : ZMod q)) -
          if χ = 1 then (M t : ℂ) else 0‖ ^ 2 := by
  calc
    _ ≤ ∑ t ∈ T, (q : ℝ) / q.totient * ∑ χ : DirichletCharacter ℂ q,
        ‖(∑ n ∈ W t, (ν n : ℂ) * χ (n : ZMod q)) -
          if χ = 1 then (M t : ℂ) else 0‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact gauss_actual_error_sq_le (W t) ν r hr (M t) (hs t ht)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

#print axioms gaussError_energy_le
#print axioms gaussError_energy_of_bound
#print axioms gauss_actual_error_energy_le
end LeanLab.Grimmelt2019.MainTerm
