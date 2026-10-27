/-
P0016 Pintz 2018, arXiv 1804.09084v2, unit U-6749, cloud VERIFY 20261020T2217Z-cloud52 of
PC run 20261020T2004Z-7678 unit U-1278, `Pintz2018Reduction.lean`.

Confirming lemma: the lab's `EventuallyBelow`, indexed by natural `X`, gives the paper's (1.9)
for every real `X > X₂`, with `E(X)` read as `E(⌊X⌋)`, the count of even `n ≤ X`.
So the natural-number encoding of Theorem 1 loses nothing. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ExceptionalSet.Statements

namespace LeanLab.ExceptionalSet.Pintz2018Verify
open Real

/-- (1.9) over real `X`: `EventuallyBelow θ` with `θ ≥ 0` gives `E(⌊X⌋) < X^θ` for all real
`X ≥ X₂`. -/
theorem real_form {θ : ℝ} (hθ : 0 ≤ θ) (h : EventuallyBelow θ) :
    ∃ X2 : ℝ, ∀ x : ℝ, X2 ≤ x → (E ⌊x⌋₊ : ℝ) < x ^ θ := by
  obtain ⟨X0, hX0⟩ := h
  refine ⟨X0, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx
  have hfl : X0 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have h1 := hX0 ⌊x⌋₊ hfl
  have h2 : ((⌊x⌋₊ : ℕ) : ℝ) ^ θ ≤ x ^ θ :=
    rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0) hθ
  linarith

end LeanLab.ExceptionalSet.Pintz2018Verify

#print axioms LeanLab.ExceptionalSet.Pintz2018Verify.real_form
