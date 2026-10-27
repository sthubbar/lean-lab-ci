/-
P0100, Dudek 2014. CLOUD 20261021T0017Z-cloud54, unit U-6793, T1.
The retired statements `theorem2_stmt` and `theorem2_large_stmt` of Statements.lean, PROVED
CONDITIONAL ON the Hasanalizade-Shen-Wong N(T) bound `HSWN70 gZ` only, through CLOUD
20261020T1717Z-cloud47's `theorem2_of_RH_hsw` in SigmaHSWDownstream.lean, wrapped as
Retired2.lean wraps `theorem1_stmt`. This replaces the input `TrudgianN70 gZ` of Retired.lean,
from Trudgian 2014, which Hasanalizade, Shen and Wong report rests on an error, and it needs no
Schoenfeld input. RH stays the hypothesis inside each statement. AI wrote this Lean code.
Binary Goldbach is OPEN.
-/
import LeanLab.Dudek2014.Statements
import LeanLab.Dudek2014.SigmaHSWDownstream

namespace LeanLab.Dudek2014.Retired3

open LeanLab.Dudek2014.SigmaH (HSWN70)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ)

/-- Dudek 2014 Theorem 2 as stated in Statements.lean, CONDITIONAL ON `HSWN70 gZ`. -/
theorem theorem2_stmt_of_hsw (hN : HSWN70 gZ) : LeanLab.Dudek2014.theorem2_stmt :=
  fun hRH => LeanLab.PNTPort.ExplicitPsi1.Trivial.theorem2_of_RH_hsw hRH hN

/-- The analytic range form, CONDITIONAL ON `HSWN70 gZ`. -/
theorem theorem2_large_stmt_of_hsw (hN : HSWN70 gZ) : LeanLab.Dudek2014.theorem2_large_stmt :=
  fun hRH x hx => LeanLab.PNTPort.ExplicitPsi1.Trivial.theorem2_of_RH_hsw hRH hN x (by linarith)

end LeanLab.Dudek2014.Retired3
