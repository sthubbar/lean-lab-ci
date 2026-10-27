/-
P0066 Vaughan 1977, 27 primes, through the Riesel-Vaughan 1983 chain: `RS33`, `Lemma6i` and
`Lemma6ii` discharged. Unit U-1391, PC run 20261021T1003Z-20044, track T1. AI-written Lean code,
Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN. KNOWN mathematics.

CONDITIONAL, counted apart: `vaughan1977_U1391`, `vaughan1977_stmt`, CONDITIONAL ON Lemma 5 at the
four rows of Lemma 8, `Table230`, `Lemma9P`, `Lemma14P`, `RS1975Cor2Thm7` and `DusartThm52k2`.
`vaughan1977_of_RV` had `Lemma6i`, `Lemma6ii` and `RS33` in place of the last two: `RS33` now
follows from `RS1975Cor2Thm7` by Common/U1391RS33, and Lemma 6 from the two θ bounds by
RieselVaughan1983/Lemma6Theta.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Route
import LeanLab.Common.U1391RS33

namespace LeanLab.SchnirelmannBounds.U1391

open LeanLab.RieselVaughan1983 LeanLab.RieselVaughan1983.Lemma6Theta LeanLab.Common.ThetaWindow
open LeanLab.SchnirelmannBounds.Vaughan1977

/-- **`vaughan1977_stmt`, every `n > 1` at most 27 primes, CONDITIONAL ON** Lemma 5 at four rows,
`Table230`, `Lemma9P`, `Lemma14P`, `RS1975Cor2Thm7` and `DusartThm52k2`. -/
theorem vaughan1977_U1391 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (hTab : Table230) (h9 : Lemma9P) (h14 : Lemma14P) (hRS75 : RS1975Cor2Thm7)
    (hD : DusartThm52k2) : LeanLab.SchnirelmannBounds.vaughan1977_stmt :=
  vaughan1977_of_RV h24 h42 h278 h396 (lemma6i_of_rs_dusart hRS75 hD) (lemma6ii_of_dusart hD)
    hTab (LeanLab.Common.U1391.rs33_of_rs1975 hRS75) h9 h14

end LeanLab.SchnirelmannBounds.U1391
