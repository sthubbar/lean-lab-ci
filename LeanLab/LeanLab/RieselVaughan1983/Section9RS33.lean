/-
P0032 Riesel-Vaughan 1983, the 18-prime Theorem with `Table230Big` PROVED and the cited
Rosser-Schoenfeld 1962 (3.3) `RS33` discharged by Common/U1391RS33 `rs33_of_rs1975`.
Unit U-1397, PC run 20261021T1103Z-29422, track T1. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN. KNOWN mathematics.

CONDITIONAL, counted apart:
* `theorem_RS5`: every even number is a sum of at most eighteen primes, CONDITIONAL ON Lemma 5
  at four rows `Lemma5Used`, `Lemma5Neg`, and the two θ bounds `RS1975Cor2Thm7` and
  `DusartThm52k2` only. `theorem_LS4` of Section9Big had `RS33` as a further input.
* `corollary19_RS5`: the nineteen prime form under the same inputs.
-/
import LeanLab.RieselVaughan1983.Section9Big
import LeanLab.Common.U1391RS33

namespace LeanLab.RieselVaughan1983.Section9RS33

open LeanLab.RieselVaughan1983 LeanLab.RieselVaughan1983.Lemma6Theta
  LeanLab.Common.ThetaWindow LeanLab.RieselVaughan1983.Section9Big

/-- **The Theorem**, CONDITIONAL ON `Lemma5Used` at rows 24, 42, 278, 396, `Lemma5Neg`,
`RS1975Cor2Thm7` and `DusartThm52k2` only. -/
theorem theorem_RS5 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (hRS75 : RS1975Cor2Thm7) (hD : DusartThm52k2) : Theorem :=
  theorem_LS4 h24 h42 h278 h396 h5 (LeanLab.Common.U1391.rs33_of_rs1975 hRS75) hRS75 hD

/-- The nineteen prime form under the same inputs. -/
theorem corollary19_RS5 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (hRS75 : RS1975Cor2Thm7) (hD : DusartThm52k2) : Corollary19 :=
  corollary19_LS4 h24 h42 h278 h396 h5 (LeanLab.Common.U1391.rs33_of_rs1975 hRS75) hRS75 hD

end LeanLab.RieselVaughan1983.Section9RS33
