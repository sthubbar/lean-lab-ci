/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 178 to 179, iteration of the nonnegative transfer recurrence.
-/
import Mathlib

namespace LeanLab.PlattTrudgian2014

open Finset

/-- A finite nonnegative recurrence preserves a supplied Perron upper bound. -/
theorem transfer_iterate125 {ι : Type*} [Fintype ι] (U : ι → ι → ℝ)
    (w : ι → ℝ) (r C : ℝ) (v : ℕ → ι → ℝ)
    (hU : ∀ i j, 0 ≤ U i j) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbase : ∀ i, v 0 i ≤ C * w i)
    (hstep : ∀ L i, v (L + 1) i = ∑ j, U i j * v L j)
    (hcert : ∀ i, (∑ j, U i j * w j) ≤ r * w i) (L : ℕ) (i : ι) :
    v L i ≤ C * r ^ L * w i := by
  induction L generalizing i with
  | zero => simpa using hbase i
  | succ L ih =>
    rw [hstep]
    calc
      _ ≤ ∑ j, U i j * (C * r ^ L * w j) :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hU i j)
      _ = (C * r ^ L) * ∑ j, U i j * w j := by rw [mul_sum]; apply sum_congr rfl; intro j _; ring
      _ ≤ (C * r ^ L) * (r * w i) :=
        mul_le_mul_of_nonneg_left (hcert i) (mul_nonneg hC (pow_nonneg hr L))
      _ = C * r ^ (L + 1) * w i := by rw [pow_succ]; ring

#print axioms transfer_iterate125

end LeanLab.PlattTrudgian2014
