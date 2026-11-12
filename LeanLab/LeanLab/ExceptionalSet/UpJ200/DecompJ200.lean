import Mathlib
import LeanLab.ExceptionalSet.BrudernPerelli1998
import LeanLab.ExceptionalSet.State1539

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
The only definition of `LeanLab.ExceptionalSet.DecompJ200` used by the chain behind
`Decomp467a.truncated_moment_of_karacuba` is `window`; it is copied here verbatim so that the
copies in `UpJ200` need not import `DecompJ200`. `DecompJ200.window` and this copy are equal by
definition. AI wrote this Lean code. Goldbach is open. -/

namespace LeanLab.ExceptionalSet.UpJ200.DecompJ200

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998
open LeanLab.ExceptionalSet.U1539 (Sp majorArcs Kfun nu calE eC)

attribute [local instance] Classical.propDecidable

/-- COPY of `DecompJ200.window`. The window of section 5, p. 366: `n ≤ 2N` with
`X/2 < ν_n ≤ X`, `X = F(N)`. -/
noncomputable def window (γ : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun n => F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)

end LeanLab.ExceptionalSet.UpJ200.DecompJ200
