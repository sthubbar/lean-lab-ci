import LeanLab.BakerHarmanPintz1997.Statements

/-!
P0069 encoding repair, U-7305. `Lemma2` and `Lemma5` now ask `2 ≤ F x ≤ x` only for large `x`,
the standing convention of p. 11, in place of the unsatisfiable global range found by CODEX
task38. This file records that the repaired range hypothesis has a witness.
-/

namespace LeanLab.BakerHarmanPintz1997

/-- The repaired eventual length range is satisfiable: `F x = x` meets it from `x = 2` on. -/
theorem ev_length_range_witness : Ev (fun x : ℝ => 2 ≤ x ∧ x ≤ x) :=
  ⟨2, fun _ hx => ⟨hx, le_rfl⟩⟩

end LeanLab.BakerHarmanPintz1997
