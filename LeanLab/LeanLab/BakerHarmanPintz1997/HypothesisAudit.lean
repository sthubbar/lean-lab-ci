/-
P0069 encoding audit of the global length range in Lemma2 and Lemma5.
The paper uses large positive x. The predicates quantified this range over every real x until
U-7305 of CLOUD 019VSv5w, which made it eventual; see RangeRepair.lean.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Statements

namespace LeanLab.BakerHarmanPintz1997

/-- The global length range of Lemma2 and Lemma5 before U-7305 has no witness. -/
theorem not_global_length_range (F : ℝ → ℝ) :
    ¬ (∀ x : ℝ, 2 ≤ F x ∧ F x ≤ x) := by
  intro h
  obtain ⟨hlo, hhi⟩ := h 0
  linarith

#print axioms not_global_length_range
end LeanLab.BakerHarmanPintz1997
