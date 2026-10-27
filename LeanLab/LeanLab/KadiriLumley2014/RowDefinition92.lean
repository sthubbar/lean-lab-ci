/-
P0059 page 1 Theorem 1.1. Existing sealed definition moved without change.
AI wrote this Lean code, CODEX task92, 2026-10-26.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.KadiriLumley2014
open Real

/-- Theorem 1.1 for one Table 2 row: for every `x > x0` there is a prime `p` with
`(1 - 1/Δ) x < p < x`. The theorem needs `x0 ≥ 4 · 10^18`. -/
def KLRow (x0 Δ : ℝ) : Prop :=
  ∀ x : ℝ, x0 < x → ∃ p : ℕ, p.Prime ∧ (1 - 1 / Δ) * x < p ∧ (p : ℝ) < x

end LeanLab.KadiriLumley2014
