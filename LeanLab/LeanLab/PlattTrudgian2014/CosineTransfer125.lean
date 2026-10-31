/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 177 to 179, Lemma 5, with base two and the explicit Taylor majorant.
-/
import LeanLab.PlattTrudgian2014.Polynomial125

namespace LeanLab.PlattTrudgian2014

open Finset

/-- Half period averaging removes the odd combined cosine frequencies. -/
theorem cos_product_half_average125 (n j : ℕ) (x : ℝ) :
    (Real.cos (n * x) * Real.cos (j * x) +
      Real.cos (n * (x + Real.pi)) * Real.cos (j * (x + Real.pi))) / 2 =
      (1 + (-1 : ℝ) ^ (n + j)) / 4 *
        (Real.cos ((n + j : ℕ) * x) + Real.cos (((n : ℝ) - j) * x)) := by
  have hn : Real.cos (n * (x + Real.pi)) = (-1 : ℝ) ^ n * Real.cos (n * x) := by
    rw [mul_add, Real.cos_add_nat_mul_pi]
  have hj : Real.cos (j * (x + Real.pi)) = (-1 : ℝ) ^ j * Real.cos (j * x) := by
    rw [mul_add, Real.cos_add_nat_mul_pi]
  have hp : Real.cos (n * x) * Real.cos (j * x) =
      (Real.cos ((n + j : ℕ) * x) + Real.cos (((n : ℝ) - j) * x)) / 2 := by
    rw [show ((n + j : ℕ) : ℝ) * x = n * x + j * x by push_cast; ring,
      show ((n : ℝ) - j) * x = n * x - j * x by ring]
    rw [Real.cos_add, Real.cos_sub]
    ring
  calc
    _ = (1 + (-1 : ℝ) ^ (n + j)) * (Real.cos (n * x) * Real.cos (j * x)) / 2 := by
      rw [hn, hj, pow_add]
      ring
    _ = _ := by rw [hp]; ring

#print axioms cos_product_half_average125

end LeanLab.PlattTrudgian2014
