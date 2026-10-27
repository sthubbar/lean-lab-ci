/-
The logical and numeric limits of the existing checker chains for P0005 and P0042.
P0005 abstract page 2033. P0042 upper bound page 428.
The square-free predicate and B2 are the local checker definitions.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Verifications.U1437Fast.Sieve
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.CheckerLimitsTask72

/-- A prime plus square-free witness can have a composite remainder. -/
theorem squarefree_remainder_can_be_composite :
    Nat.Prime 2 ∧ (2 : ℕ) < 12 ∧ Squarefree (12 - 2 : ℕ) ∧
      ¬ Nat.Prime (12 - 2) := by
  decide +kernel

/-- The existing P32 prime-window soundness bound is below the P0042 endpoint. -/
theorem p32_below_p0042_endpoint : ¬ (2 * 10 ^ 10 ≤ Top50.Bits.B2) := by
  norm_num [Top50.Bits.B2]

/-- The existing P32 prime-window soundness bound is below the P0005 endpoint. -/
theorem p32_below_p0005_endpoint : ¬ (4 * 10 ^ 18 ≤ Top50.Bits.B2) := by
  norm_num [Top50.Bits.B2]

end LeanLab.Verifications.CheckerLimitsTask72
