/-
P0032 Riesel-Vaughan 1983: the cited Rosser-Schoenfeld 1962 (3.3) `RS33` discharged by
Common/U1391RS33 `rs33_of_rs1975`, which needs only `RS1975Cor2Thm7`, already an input here.
Unit U-1391, PC run 20261021T1003Z-20044, track T1. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN. KNOWN mathematics.

CONDITIONAL, counted apart:
* `rs33_of_rs75`: `RS33`, CONDITIONAL ON `RS1975Cor2Thm7`.
* `lemma7_of_rs75`: Lemma 7, `N(x) > x/18` for `2 ≤ x ≤ e^27`, CONDITIONAL ON `RS1975Cor2Thm7`;
  was CONDITIONAL ON `RS33`.
* `theorem_U1391`, `corollary19_U1391`: the 18-prime Theorem and the 19-prime Corollary by the
  `Final.lean` route, CONDITIONAL ON Lemma 5 at four rows, `Lemma5Neg`, `Table230`, `Lemma14P`,
  `RS1975Cor2Thm7` and `DusartThm52k2`; `theorem_of_lemma5_14` had `Lemma6i`, `Lemma6ii` and
  `RS33` in place of the last two.
-/
import LeanLab.RieselVaughan1983.Final
import LeanLab.Common.U1391RS33

namespace LeanLab.RieselVaughan1983.U1391

open LeanLab.RieselVaughan1983 LeanLab.RieselVaughan1983.Lemma6Theta LeanLab.Common.ThetaWindow

/-- `RS33`, CONDITIONAL ON `RS1975Cor2Thm7`. The two Props have the same statement. -/
theorem rs33_of_rs75 (hRS : RS1975Cor2Thm7) : RS33 := LeanLab.Common.U1391.rs33_of_rs1975 hRS

/-- Lemma 7, CONDITIONAL ON `RS1975Cor2Thm7`. -/
theorem lemma7_of_rs75 (hRS : RS1975Cor2Thm7) : Lemma7 := lemma7_of_RS (rs33_of_rs75 hRS)

/-- **The Theorem**, every even number at most 18 primes, CONDITIONAL ON Lemma 5 at five rows,
`Table230`, `Lemma14P`, `RS1975Cor2Thm7` and `DusartThm52k2`. -/
theorem theorem_U1391 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (hTab : Table230) (h14 : Lemma14P) (hRS75 : RS1975Cor2Thm7)
    (hD : DusartThm52k2) : Theorem :=
  theorem_of_lemma5_14 h24 h42 h278 h396 h5 (lemma6i_of_rs_dusart hRS75 hD)
    (lemma6ii_of_dusart hD) hTab (rs33_of_rs75 hRS75) h14

/-- The nineteen prime form under the same inputs. -/
theorem corollary19_U1391 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (hTab : Table230) (h14 : Lemma14P) (hRS75 : RS1975Cor2Thm7)
    (hD : DusartThm52k2) : Corollary19 :=
  corollary19_of_lemmas h24 h42 h278 h396 (lemma6i_of_rs_dusart hRS75 hD)
    (lemma6ii_of_dusart hD) hTab (rs33_of_rs75 hRS75) (lemma9_of h5) h14

end LeanLab.RieselVaughan1983.U1391
