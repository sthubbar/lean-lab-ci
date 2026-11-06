/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 178, regrouping a single cosine product before summing coefficients.
-/
import LeanLab.PlattTrudgian2014.CosineTransfer125

namespace LeanLab.PlattTrudgian2014

open Finset

/-- P0026 pages 178 to 179, contribution of one polynomial mode to a matrix entry. -/
def halfMode380 (i : Fin 16) (k : Fin 17) (j : Fin 16) : ℚ :=
  ((if (k : ℤ) = 2 * (j : ℤ) - i then 1 else 0) +
    (if (k : ℤ) = 2 * (j : ℤ) + i then 1 else 0) +
    (if j = 0 then 0 else if (k : ℤ) = (i : ℤ) - 2 * j then 1 else 0)) / 2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
/-- P0026 page 178 h star, exact finite routing of even frequencies. -/
theorem half_mode_routing380 : ∀ i : Fin 16, ∀ k : Fin 17, ∀ j : Fin 16,
    halfMode380 i k j = if Even ((i : ℕ) + (k : ℕ)) then
      ((if (j : ℕ) = ((i : ℕ) + (k : ℕ)) / 2 then 1 else 0) +
        (if (j : ℕ) = Int.natAbs ((i : ℤ) - k) / 2 then 1 else 0)) / 2 else 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
/-- P0026 page 178, coefficient collection with the zero column counted once. -/
theorem half_transfer_mode_sum380 (i j : Fin 16) :
    halfTransfer125 i j = ∑ k : Fin 17, halfCoeff125 k * halfMode380 i k j := by
  have hall : ∀ i j : Fin 16,
      halfTransfer125 i j = ∑ k : Fin 17, halfCoeff125 k * halfMode380 i k j := by
    decide +kernel
  exact hall i j

#print axioms half_mode_routing380
#print axioms half_transfer_mode_sum380

end LeanLab.PlattTrudgian2014
