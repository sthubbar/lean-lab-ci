/-
Audit U-1058, PC run 20261019T1204Z-858. The cited titles of P0063 van der Corput, P0064
Chudakov, P0091 Estermann and Theorem 4.3 of P0029 Bhowmik-Grimmelt, kept until now as `sorry`
theorems in Statements.lean and BhowmikGrimmelt2026.lean, are now `_stmt` Props there and are
PROVED here, unconditional, from the lab's own Siegel-Walfisz chain,
`PNTPort/PsiChi/CitedDischarged.lean`, cloud unit U-5211, rebuilt on the PC in U-1038.
These are Heath-Brown's route through Siegel-Walfisz, NOT formalizations of the 1937 and 1938
papers' own proofs; the implied constant is ineffective. Known mathematics.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.PNTPort.PsiChi.CitedDischarged
import LeanLab.Common.GoldbachSmall

namespace LeanLab.ExceptionalSet

/-- P0063 van der Corput, title: the non-Goldbach evens up to `X` are `o(X)`. -/
theorem vanDerCorput : vanDerCorput_stmt := LeanLab.PNTPort.PsiChi.exceptional_densityZero

/-- P0064 Chudakov 1938, title: density zero. -/
theorem chudakov : chudakov_stmt := LeanLab.PNTPort.PsiChi.exceptional_densityZero

/-- P0063 and P0064 in the log power strength: `E X ≪_A X / (log X)^A` for every `A > 0`. -/
theorem vanDerCorput_chudakov_strong : vanDerCorput_chudakov_strong_stmt :=
  LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving

/-- P0091 Estermann 1938 in the classical log power form. -/
theorem estermann : estermann_stmt := LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving

/-- Faithfulness: the Props are exactly the strengths defined in Statements.lean. -/
example : vanDerCorput_stmt = DensityZero := rfl
example : estermann_stmt = LogPowerSaving := rfl

/-- Vacuity test: the count these bounds control is a real count, `E 1000 = 0` from the lab's
kernel check of even Goldbach to 1000. -/
example : E 1000 = 0 := E_eq_zero_of_upTo evenGoldbachUpTo_1000 1000 le_rfl

namespace BG2026

/-- P0029 Theorem 4.3, Chudakov, van der Corput, Estermann, page 17. -/
theorem theorem43 : theorem43_stmt := LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving

example : theorem43_stmt = LogPowerSaving := rfl

end BG2026

end LeanLab.ExceptionalSet

#print axioms LeanLab.ExceptionalSet.vanDerCorput
#print axioms LeanLab.ExceptionalSet.chudakov
#print axioms LeanLab.ExceptionalSet.vanDerCorput_chudakov_strong
#print axioms LeanLab.ExceptionalSet.estermann
#print axioms LeanLab.ExceptionalSet.BG2026.theorem43
