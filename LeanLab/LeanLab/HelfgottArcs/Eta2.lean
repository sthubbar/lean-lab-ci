/-
`η₁ *_M η₁ = η₂`, the smoothing identity of 1205.5252 eq 1.4 and 1305.2897.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.HelfgottArcs.Statements

namespace LeanLab.HelfgottArcs
open MeasureTheory Set

/-- Compatibility name for the convolution identity now proved in Statements.lean. -/
theorem eta2_eq_mconv' (t : ℝ) (ht : 0 < t) : mconv eta1 eta1 t = eta2 t :=
  eta2_eq_mconv t ht

end LeanLab.HelfgottArcs
