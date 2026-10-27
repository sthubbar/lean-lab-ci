/-
P0100, Dudek 2014. CLOUD 20261020T2018Z-cloud50, unit U-6739, T1.
The three `sorry` theorems `theorem1`, `theorem3` and `abstract_c3` of Statements.lean are retired
into the statements `theorem1_stmt`, `theorem3_stmt` and `abstract_c3_stmt`; here all three are
PROVED CONDITIONAL ON the Hasanalizade-Shen-Wong N(T) bound `HSWN70 gZ`, through this session's
U-6722 `theorem1_of_RH_hsw` and U-6730 `abstract_c3_of_RH_hsw`, `theorem3_of_RH_hsw`.
RH stays the hypothesis inside each statement. AI wrote this Lean code.
-/
import LeanLab.Dudek2014.Statements
import LeanLab.Dudek2014.AbstractC3HSW

namespace LeanLab.Dudek2014.Retired2

open LeanLab.Dudek2014.SigmaH (HSWN70)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ)

/-- Dudek 2014 Theorem 1 as stated in Statements.lean, CONDITIONAL ON `HSWN70 gZ`. -/
theorem theorem1_stmt_of (hN : HSWN70 gZ) : LeanLab.Dudek2014.theorem1_stmt :=
  fun hRH => LeanLab.Dudek2014.Theorem1H.theorem1_of_RH_hsw hRH hN

/-- Dudek 2014 Theorem 3 as stated in Statements.lean, CONDITIONAL ON `HSWN70 gZ`. -/
theorem theorem3_stmt_of (hN : HSWN70 gZ) : LeanLab.Dudek2014.theorem3_stmt :=
  fun hRH => LeanLab.Dudek2014.AbstractC3.theorem3_of_RH_hsw hRH hN

/-- The abstract's `c = 3 + ε` as stated in Statements.lean, CONDITIONAL ON `HSWN70 gZ`. -/
theorem abstract_c3_stmt_of (hN : HSWN70 gZ) : LeanLab.Dudek2014.abstract_c3_stmt :=
  fun hRH => LeanLab.Dudek2014.AbstractC3.abstract_c3_of_RH_hsw hRH hN

end LeanLab.Dudek2014.Retired2
