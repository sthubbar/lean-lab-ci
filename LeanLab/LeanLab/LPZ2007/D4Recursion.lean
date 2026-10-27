/-
P0045, journal page 777, display 20.
Split a tuple of exponents into one exponent and its remaining coordinates.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.D4Tail

namespace LeanLab.LPZ2007.D4Recursion

open Finset
open LeanLab.LPZ2007 LeanLab.LPZ2007.D4Tail LeanLab.LPZ2007.Eq14FromCor42

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The divisor count is a sum of single exponent counts over the other coordinates. -/
theorem count_succ_eq (d j M N : ℕ) :
    (#{ν ∈ tuples (j + 1) M | d ∣ N - pow2sum ν} : ℝ) =
      ∑ t ∈ tuples j M, (oneCount d M (N - pow2sum t) : ℝ) := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_tuples_succ]
  apply sum_congr rfl
  intro t _
  unfold oneCount
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply sum_congr rfl
  intro a _
  rw [pow2sum_cons]
  rw [show N - (2 ^ a + pow2sum t) = (N - pow2sum t) - 2 ^ a by omega]

end
end LeanLab.LPZ2007.D4Recursion

#print axioms LeanLab.LPZ2007.D4Recursion.count_succ_eq
