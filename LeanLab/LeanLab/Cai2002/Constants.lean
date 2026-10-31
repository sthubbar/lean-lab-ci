/-
P0044, Cai 2002: all four Section 4 integral constants at θ = 0.95, PROVED.
AI-written Lean code, Claude, run 20261018T2303Z-8776. Checked only by the Lean kernel.
-/
import LeanLab.Cai2002.Integrals
import LeanLab.Cai2002.Integral414
import LeanLab.Cai2002.Integral44
import LeanLab.Cai2002.Integral47

namespace LeanLab.Cai2002

/-- (4.4), (4.7), (4.14), (4.15) together. -/
theorem section4_constants : Eq44Const ∧ Eq47Const ∧ Eq414Const ∧ Eq415Const :=
  ⟨eq44, eq47, eq414, eq415⟩

end LeanLab.Cai2002
