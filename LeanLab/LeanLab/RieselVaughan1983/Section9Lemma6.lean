/-
P0032 Riesel-Vaughan 1983, the 18-prime Theorem with Lemma 6 discharged through Lemma6Theta.lean.
Unit U-6733, CLOUD 20261020T2113Z-cloud51, track T1. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

CONDITIONAL, counted apart:
* `theorem_LS3`: every even number is a sum of at most eighteen primes, CONDITIONAL ON Lemma 5
  at five rows, `Table230Big`, Rosser-Schoenfeld (3.3) `RS33`, and the two θ bounds
  `RS1975Cor2Thm7` and `DusartThm52k2` in place of Lemma 6 (i) and (ii).
* `corollary19_LS3`: the nineteen prime form under the same inputs.
KNOWN mathematics.
-/
import LeanLab.RieselVaughan1983.Section9LS2
import LeanLab.RieselVaughan1983.Lemma6Theta

namespace LeanLab.RieselVaughan1983.Section9Lemma6

open LeanLab.RieselVaughan1983 LeanLab.RieselVaughan1983.Section9LS2
  LeanLab.RieselVaughan1983.Table230Small LeanLab.RieselVaughan1983.Lemma6Theta
  LeanLab.Common.ThetaWindow

/-- **The Theorem**, CONDITIONAL ON Lemma 5 at five rows, `Table230Big`, `RS33`,
`RS1975Cor2Thm7` and `DusartThm52k2`. -/
theorem theorem_LS3 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (hT : Table230Big) (hRS : RS33) (hRS75 : RS1975Cor2Thm7)
    (hD : DusartThm52k2) : Theorem :=
  theorem_LS2 h24 h42 h278 h396 h5 (lemma6i_of_rs_dusart hRS75 hD) (lemma6ii_of_dusart hD) hT hRS

/-- The nineteen prime form under the same inputs. -/
theorem corollary19_LS3 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (hT : Table230Big) (hRS : RS33) (hRS75 : RS1975Cor2Thm7)
    (hD : DusartThm52k2) : Corollary19 :=
  corollary19_LS2 h24 h42 h278 h396 h5 (lemma6i_of_rs_dusart hRS75 hD) (lemma6ii_of_dusart hD)
    hT hRS

end LeanLab.RieselVaughan1983.Section9Lemma6
