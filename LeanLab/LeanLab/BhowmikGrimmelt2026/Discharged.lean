/-
Audit U-1058, PC run 20261019T1204Z-858. Theorem 4.3 of P0029, page 17, Chudakov, van der
Corput, Estermann, `|𝓔(X)| ≪_A X (log X)^{-A}`, was a cited `sorry` in Statements.lean; it is now
the Prop `theorem43_stmt` there and PROVED here, unconditional, from the lab's Siegel-Walfisz
chain, `PNTPort/PsiChi/CitedDischarged.lean`. Known mathematics, ineffective constant.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import LeanLab.PNTPort.PsiChi.CitedDischarged

namespace LeanLab.BhowmikGrimmelt2026

theorem theorem43 : theorem43_stmt := LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving

example : theorem43_stmt = LeanLab.ExceptionalSet.LogPowerSaving := rfl

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.theorem43
