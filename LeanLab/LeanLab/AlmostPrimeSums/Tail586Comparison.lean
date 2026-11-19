import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum

/-!
AI wrote this Lean code for CODEX task586. Goldbach is open.
An exact scalar check for the proposed pointwise transfer between two
different truncations. It does not negate any Rosser moment statement.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset

/-- The ninth degree and first degree lower alternating truncations on
twelve variables have values minus fifty five and minus eleven.
This scalar ordering obstructs a direct monotonicity argument for
lower truncations. Derived finite check for Heath Brown pp. 31 to 32
and Opera de Cribro p. 68, not a statement printed in either source. -/
theorem truncation_transfer_obstruction586 :
    (∑ k ∈ range 10, ((-1) ^ k * (12 : ℕ).choose k : ℤ)) = -55 ∧
      (∑ k ∈ range 2, ((-1) ^ k * (12 : ℕ).choose k : ℤ)) = -11 ∧
      (-55 : ℤ) < -11 := by
  have h9 := Int.alternating_sum_range_choose_eq_choose (n := 11) (m := 9)
  have h1 := Int.alternating_sum_range_choose_eq_choose (n := 11) (m := 1)
  norm_num at h9 h1
  exact ⟨h9, h1, by norm_num⟩

end LeanLab.AlmostPrimeSums.Decomp1527b
