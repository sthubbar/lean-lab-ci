import LeanLab.ChenDoubleSieve.Task587TailFiveFormula

/-!
A finite delay-integral certificate for Wu 2004 Lemma 2.10 page 9.
Source: https://arxiv.org/abs/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Finset
namespace LeanLab.ChenDoubleSieve.Task587

/-- The 192 scalar panels run from three through four. Wu 2004 page 9, derived grid. -/
def tailFiveNode (j : ℕ) : ℚ := 3 + (j : ℚ) / 192

/-- Exact rational upper sum for the scalar delay integral. Wu 2004 page 9. -/
def tailFiveSum : ℚ := ∑ j ∈ range 192,
  tailFiveCapQ (tailFiveNode j) (tailFiveNode (j + 1)) / 192

/-- The directed rational delay-integral sum fits its budget.
Wu 2004 page 9, derived kernel checked certificate. -/
theorem tailFive_certificate : tailFiveSum ≤ (5625 / 10000 : ℚ) := by
  decide +kernel

end LeanLab.ChenDoubleSieve.Task587
