/-
Yamada's explicit Chen theorem, the cited Rosser-Schoenfeld 1962 input `RS62` discharged:
`RS62` has the same statement as RieselVaughan1983 `RS33` and follows from Rosser-Schoenfeld 1975
`RS1975Cor2Thm7`, `θ(t) ≥ t - t/(40 log t)` for `t ≥ 678407`, by Common/U1391RS33.
Unit U-1391, PC run 20261021T1003Z-20044, track T1. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN. KNOWN mathematics.

CONDITIONAL, counted apart:
* `rs62_of_rs75`: `RS62`, CONDITIONAL ON `RS1975Cor2Thm7`.
* `thm48_of_rs75`: Yamada (48), `|A| > N/log N` for even `N > exp exp 36`, CONDITIONAL ON
  `RS1975Cor2Thm7`; `thm48_of_RS62` was CONDITIONAL ON `RS62`.
* `yamada_of_sieve_rs75`: Yamada Theorem 1.1 CONDITIONAL ON Theorems 5.1, 6.1, 7.1 and
  `RS1975Cor2Thm7`; `yamada_of_sieve_RS` had `RS62` in place of the last.
-/
import LeanLab.ChenExplicit.Thm48
import LeanLab.Common.U1391RS33

namespace LeanLab.ChenExplicit.Yamada.U1391

open LeanLab.ChenExplicit.Yamada LeanLab.RieselVaughan1983.Lemma6Theta

/-- `RS62`, CONDITIONAL ON `RS1975Cor2Thm7`. -/
theorem rs62_of_rs75 (hRS : RS1975Cor2Thm7) : RS62 := LeanLab.Common.U1391.rs33_of_rs1975 hRS

/-- Yamada (48), CONDITIONAL ON `RS1975Cor2Thm7`. -/
theorem thm48_of_rs75 (hRS : RS1975Cor2Thm7) : Thm48 := thm48_of_RS62 (rs62_of_rs75 hRS)

/-- **Yamada Theorem 1.1**, CONDITIONAL ON Theorems 5.1, 6.1, 7.1 and `RS1975Cor2Thm7`. -/
theorem yamada_of_sieve_rs75 (hRS : RS1975Cor2Thm7) (h51 : Thm51) (h61 : Thm61) (h71 : Thm71) :
    Yamada :=
  yamada_of_sieve_RS (rs62_of_rs75 hRS) h51 h61 h71

end LeanLab.ChenExplicit.Yamada.U1391
