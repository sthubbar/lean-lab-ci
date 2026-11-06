import LeanLab.Halupczok2012.U1496PP
import LeanLab.PNTPort.Gallagher.Basic

/-!
Perelli Pintz 1993 page 43, the circle method definitions.
The additive character is reused from PNTPort.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp398a

open Finset MeasureTheory
open scoped Classical ArithmeticFunction.vonMangoldt

/-- Perelli Pintz page 43, the additive character e of t. -/
noncomputable def phase (t : ℝ) : ℂ :=
  LeanLab.PNTPort.LargeSieve.e t

/-- Perelli Pintz page 43, the first finite polynomial S1. -/
noncomputable def firstPoly (N Y α : ℝ) : ℂ :=
  ∑ h ∈ kRange (N - Y) Y, (Λ h : ℂ) * phase ((h : ℝ) * α)

/-- Perelli Pintz page 43, the second finite polynomial S2. -/
noncomputable def secondPoly (Y α : ℝ) : ℂ :=
  ∑ j ∈ kRange 0 Y, (Λ j : ℂ) * phase ((j : ℝ) * α)

/-- Perelli Pintz page 43, the unit interval with Q equal to sqrt H over 2. -/
noncomputable def arcBase (Y ε : ℝ) : Set ℝ :=
  Set.Icc (1 / (Real.sqrt (Y ^ (1 / 3 + ε)) / 2))
    (1 + 1 / (Real.sqrt (Y ^ (1 / 3 + ε)) / 2))

/-- Perelli Pintz page 43, major arcs with B equal to 3 over epsilon times 2A + 25.
The intersection with the base interval makes the partition exact at every parameter. -/
noncomputable def majorArcs (N Y ε A : ℝ) : Set ℝ :=
  arcBase Y ε ∩ {α | ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ (3 / ε * (2 * A + 25)) ∧
    1 ≤ a ∧ a ≤ q ∧ a.Coprime q ∧
    |α - (a : ℝ) / q| < Real.log N ^ (2 * (3 / ε * (2 * A + 25))) / ((q : ℝ) * Y)}

/-- Perelli Pintz page 44, the Fourier coefficient integrated over a chosen arc set. -/
noncomputable def arcCoeff (N Y : ℝ) (m : ℕ) (arcs : Set ℝ) : ℂ :=
  ∫ α in arcs, firstPoly N Y α * secondPoly Y α * phase (-(m : ℝ) * α)

end LeanLab.Halupczok2012.Decomp398a
