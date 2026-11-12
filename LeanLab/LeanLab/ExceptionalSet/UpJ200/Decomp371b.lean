import LeanLab.ExceptionalSet.UpJ200.Decomp371a

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.Decomp371b`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
Task371 minor arc decomposition of P0082, pages 365 to 366, displays 24 to 27.
The open inputs are the discarded tail and the truncated second moment.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp371b

open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable)
open LeanLab.ExceptionalSet.U1539 (Sp majorArcs Kfun eC calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200

/-- The integral over the truncated minor arcs of P0082 page 365 display 24,
with the same P, X and Delta as the existing minorInt. -/
noncomputable def truncatedMinor (γ δ κ : ℝ) (N n : ℕ) : ℂ :=
  ∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
      Set.Icc (-(F γ N ^ (6 * δ))) (F γ N ^ (6 * δ)),
    Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
      (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ) * eC (-(α * F γ n))

end LeanLab.ExceptionalSet.UpJ200.Decomp371b
