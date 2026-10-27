/-
Nonvacuity of the generic uniform-bound hypotheses in TableBoundsTask72.
P0005 Tables 4 and 8 and P0042 Table 3 use the local minGB and prime-gap definitions.
These broad caps assert no existence of a Goldbach partition.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Verifications.PartitionConventionTask72

namespace LeanLab.Verifications.VacuityTask72

/-- The lab least-prime value is at most n, including its zero-extension case. -/
theorem minGB_le_self (n : ℕ) : minGB n ≤ n := by
  classical
  by_cases hex : ∃ p, p.Prime ∧ (n - p).Prime
  · have hp := PartitionConventionTask72.minGB_spec_of_exists hex
    have hpos := hp.2.pos
    omega
  · unfold minGB
    rw [dif_neg hex]
    exact Nat.zero_le n

/-- Concrete broad caps satisfy both generic partition-bound hypotheses. -/
theorem uniform_partition_caps :
    (∀ n : ℕ, Even n → 4 ≤ n → n ≤ 2 * 10 ^ 10 → minGB n ≤ 2 * 10 ^ 10) ∧
    (∀ n : ℕ, Even n → 4 ≤ n → n ≤ 4 * 10 ^ 18 → minGB n ≤ 4 * 10 ^ 18) := by
  constructor <;> intro n _ _ hn <;> exact (minGB_le_self n).trans hn

/-- The broad cap 4e18 satisfies the generic gap-bound hypothesis. -/
theorem uniform_gap_cap :
    ∀ p q : ℕ, p.Prime → q.Prime → p < q → q ≤ 4 * 10 ^ 18 →
      (∀ r, p < r → r < q → ¬ r.Prime) → q - p ≤ 4 * 10 ^ 18 := by
  intro p q _ _ _ hq _
  exact (Nat.sub_le q p).trans hq

end LeanLab.Verifications.VacuityTask72
