/-
P0032 Riesel-Vaughan 1983, the 18-prime Theorem with `Table230Big` discharged.
Unit U-6740, CLOUD 20261020T2113Z-cloud51, track T1. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

CONDITIONAL, counted apart:
* `theorem_LS4`: every even number is a sum of at most eighteen primes, CONDITIONAL ON Lemma 5
  at five rows, Rosser-Schoenfeld (3.3) `RS33`, and the two θ bounds `RS1975Cor2Thm7` and
  `DusartThm52k2`. The table input `Table230Big` is now PROVED in `Table230BigEval`.
* `corollary19_LS4`: the nineteen prime form under the same inputs.
KNOWN mathematics.
-/
import LeanLab.RieselVaughan1983.Section9Lemma6
import LeanLab.RieselVaughan1983.Table230BigEval

namespace LeanLab.RieselVaughan1983.Section9Big

open LeanLab.RieselVaughan1983 LeanLab.RieselVaughan1983.Section9LS2
  LeanLab.RieselVaughan1983.Table230Small LeanLab.RieselVaughan1983.Lemma6Theta
  LeanLab.Common.ThetaWindow LeanLab.RieselVaughan1983.Section9Lemma6
  LeanLab.RieselVaughan1983.Table230BigEval

/-- **The Theorem**, CONDITIONAL ON Lemma 5 at five rows, `RS33`, `RS1975Cor2Thm7` and
`DusartThm52k2`. -/
theorem theorem_LS4 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (hRS : RS33) (hRS75 : RS1975Cor2Thm7) (hD : DusartThm52k2) : Theorem :=
  theorem_LS3 h24 h42 h278 h396 h5 table230Big hRS hRS75 hD

/-- The nineteen prime form under the same inputs. -/
theorem corollary19_LS4 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (hRS : RS33) (hRS75 : RS1975Cor2Thm7) (hD : DusartThm52k2) :
    Corollary19 :=
  corollary19_LS3 h24 h42 h278 h396 h5 table230Big hRS hRS75 hD

end LeanLab.RieselVaughan1983.Section9Big
