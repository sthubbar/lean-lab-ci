import LeanLab.PNTPort.PsiChi.CitedDischarged
import LeanLab.Ternary.Statements

/-!
# P0004, Hardy-Littlewood 1923: the lab's cited statement, discharged

Lab proof, unit U-5256. AI wrote this file.

The lab states P0004 as `Ternary.hardyLittlewood : GRH → ∃ C, TernaryAbove C`, a cited `sorry`.
Its conclusion holds without the hypothesis: `PsiChi.ternary_vinogradov`, from the lab's
unconditional Siegel-Walfisz theorem, so the statement is PROVED with `GRH` unused. This is
NOT a formalization of Hardy and Littlewood's argument, and their asymptotic under GRH with its
error term is not stated in the lab; the unconditional circle method asymptotic is
`Vinogradov.vinogradov_asymptotic`. Ternary Goldbach is Helfgott's theorem; binary Goldbach is
OPEN.
-/

namespace LeanLab.PNTPort.Vinogradov

/-- The exact type of the cited `Ternary.hardyLittlewood`, proved. -/
theorem hardyLittlewood_discharged :
    LeanLab.DERZ1997.GRH → ∃ C : ℝ, LeanLab.Ternary.TernaryAbove C :=
  fun _ => LeanLab.PNTPort.PsiChi.ternary_vinogradov

/-- Type check against the cited statement, now the Prop `hardyLittlewood_stmt` since audit U-1058,
PC run 20261019T1204Z-858: fails to elaborate if the types differ. -/
example : LeanLab.Ternary.hardyLittlewood_stmt := hardyLittlewood_discharged

end LeanLab.PNTPort.Vinogradov

