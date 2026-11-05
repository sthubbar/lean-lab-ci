import Mathlib
open Finset
/-!
Task345. A compressed finite certificate for the initial proper prime power range.
Source: the error term in Schoenfeld page 356, display 5.3 star.
The intervals and bit weights are derived proof data.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task345

/-- The sum of exponent counts times ceiling base two logarithms of prime bases.
Only prime bases through the square root of N can contribute proper powers.
This is derived integer proof data for display 5.3 star on Schoenfeld page 356. -/
def powerBitSum (N : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE (Nat.sqrt N), (Nat.log p N - 1) * Nat.clog 2 p

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Nine exact weighted counts for the initial range in display 5.3 star
on Schoenfeld page 356. These endpoints are derived certificate data.
The sum is over at most 31 prime bases, so large prime tests are avoided. -/
theorem power_bit_certificate : powerBitSum 168 = 25 ∧ powerBitSum 360 = 40 ∧
    powerBitSum 840 = 56 ∧ powerBitSum 1680 = 77 ∧ powerBitSum 2808 = 105 ∧
      powerBitSum 4912 = 134 ∧ powerBitSum 7920 = 174 ∧ powerBitSum 11880 = 210 ∧
        powerBitSum 16384 = 244 := by
  decide +kernel

#print axioms LeanLab.LiuWang2002.Task345.power_bit_certificate
end LeanLab.LiuWang2002.Task345
