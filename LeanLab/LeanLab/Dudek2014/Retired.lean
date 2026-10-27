/-
P0100, Dudek 2014. PC 20261020T1603Z-26078, unit U-1246, T1.
The two `sorry` theorems `theorem2` and `theorem2_large` of Statements.lean are retired into the
statements `theorem2_stmt` and `theorem2_large_stmt`; here both are PROVED CONDITIONAL ON
Trudgian's N(T) bound `TrudgianN70` and Schoenfeld's ψ - θ bounds, through CLOUD 20261020T1518Z-cloud45's
`theorem2_of_RH_trudgian`, verified by PC U-1245. RH stays the hypothesis inside the statement.
AI wrote this Lean code.
-/
import LeanLab.Dudek2014.Statements
import LeanLab.PNTPort.ExplicitPsi1.DudekTrudgian

namespace LeanLab.Dudek2014.Retired

/-- Dudek 2014 Theorem 2 as stated in Statements.lean, CONDITIONAL ON `TrudgianN70` and `Schoenfeld`. -/
theorem theorem2_stmt_of
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld) :
    LeanLab.Dudek2014.theorem2_stmt :=
  fun hRH => LeanLab.PNTPort.ExplicitPsi1.Trivial.theorem2_of_RH_trudgian hRH hN hSch

/-- the analytic range form, CONDITIONAL ON the same two inputs -/
theorem theorem2_large_stmt_of
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld) :
    LeanLab.Dudek2014.theorem2_large_stmt :=
  fun hRH x hx => LeanLab.PNTPort.ExplicitPsi1.Trivial.theorem2_of_RH_trudgian hRH hN hSch x (by linarith)

end LeanLab.Dudek2014.Retired
