/-
Unit U-1513, PC run 20261025T0803Z-22023, P0022 Kaniecki 1995. AI-written Lean code, Claude.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
`kaniecki1995_theorem_hsw` of U1513KanieckiHSW.lean with its J_ψ hypothesis, constant 1.0069,
discharged by `SmoothT2.theorem2_u6806` of the split file U6806Theorem2Sp.lean. The monolithic
U6806Theorem2.lean needs U6743Diag.lean, which was killed for memory on this machine.
-/
import Mathlib
import LeanLab.Kaniecki1995.U1513KanieckiHSW
import LeanLab.ChirreHagen2025.U6806Theorem2Sp

namespace LeanLab.Kaniecki1995.U1513
open Real LeanLab.ChirreHagen2025
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ)
open LeanLab.Dudek2014.SigmaH (HSWN70)

/-- The same with the 1.0069 J_ψ bound discharged by `SmoothT2.theorem2_u6806`. CONDITIONAL ON
`ExplicitA`, `HadamardK`, `BPTN` under RH and `Ordinates14` for an ordinate family `γ`, the
4 · 10^18 check, Liu-Wang, and `HSWN70 gZ`, `HSWHead14 gZ`, `Ordinates14 gZ`. -/
theorem kaniecki1995_theorem_u6806_hsw {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hA : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hK : RiemannHypothesis → SmoothT2.HadamardK γ) (h14g : SmoothT2.Ordinates14 γ)
    (hB : RiemannHypothesis → Lemma26B.BPTN γ)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100))
    (hN : HSWN70 gZ) (hH : HSWHead14 gZ) (h14 : SmoothT2.Ordinates14 gZ) :
    LeanLab.Kaniecki1995.TheoremOdd ∧ LeanLab.Kaniecki1995.TheoremEven :=
  kaniecki1995_theorem_hsw
    (fun hRH => SmoothT2.theorem2_u6806 (hA hRH) (hK hRH) h14g (hB hRH)) hE hLW hN hH h14

end LeanLab.Kaniecki1995.U1513
