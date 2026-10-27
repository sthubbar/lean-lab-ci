/-
P0096 Heath-Brown 1985, pages 56 to 58 and Corollary 1: Corollary 1 from the two cited bounds
`BoundSigma3`, page 56, and `MainTerm4`, page 57, with the Siegel-Walfisz theorem 1.1.
PROVED here: corollary1_of_cited, via theorem1_of in Theorem1Chain.lean and
corollary1_of_theorem1 in Bridge.lean.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.HeathBrown1985.Theorem1Chain
import LeanLab.HeathBrown1985.Bridge

noncomputable section
namespace LeanLab.HeathBrown1985

/-- **Corollary 1 from the Σ₃ bound, the main term and Siegel-Walfisz.** -/
theorem corollary1_of_cited (h3 : BoundSigma3) (h4 : MainTerm4) (hSW : SiegelWalfisz) :
    Corollary1 :=
  corollary1_of_theorem1 (theorem1_of h3 h4 hSW)

end LeanLab.HeathBrown1985
