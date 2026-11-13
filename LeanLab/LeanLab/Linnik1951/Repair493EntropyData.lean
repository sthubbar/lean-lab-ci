/-
P0093 page 163 equation 7.11. Sealed dyadic index data moved before their proofs.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Truncation412

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- P0093 page 163 equation 7.11. Indices of the first M positive
powers whose phase lies within two to negative r of an integer. -/
noncomputable def nearIntegerIndices412 (M r : ℕ) (α : ℝ) : Finset ℕ := by
  classical
  exact (range M).filter fun m => ∃ z : ℤ,
    |α * (2 : ℝ) ^ (m + 1) - z| ≤ (1 / 2 : ℝ) ^ r

/-- P0093 page 163 equation 7.11. At phase zero every index qualifies.
This certifies that the binary concentration set is nonempty. -/
theorem near_indices_zero412 (M r : ℕ) : nearIntegerIndices412 M r 0 = range M := by
  classical
  apply Finset.filter_eq_self.mpr
  intro m hm
  exact ⟨0, by simp⟩

end LeanLab.Linnik1951
