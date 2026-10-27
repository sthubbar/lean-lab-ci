/-
P0066 Vaughan 1977, 27 primes, reached through the lab's Riesel-Vaughan 1983 chain, P0032,
by import only. The reconstructed input `VaughanDensity26` of Vaughan1977.lean follows from
Riesel-Vaughan's (1.1), which the lab proves CONDITIONAL ON named inputs. This is NOT
Vaughan's own 1977 proof, whose analytic sections are unread; it is a route to the same
statement. AI-written Lean code, Claude, 2026-10-20, run 20261020T2004Z-7678, unit U-1273.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977
import LeanLab.RieselVaughan1983.Assembly
import LeanLab.RieselVaughan1983.Section9
import LeanLab.SchnirelmannBounds.Statements

namespace LeanLab.SchnirelmannBounds.Vaughan1977
open LeanLab.RieselVaughan1983

/-- **Statement27, every `n > 1` at most 27 primes, CONDITIONAL ON** Riesel-Vaughan's
Lemma 5 at the four table rows of Lemma 8, Lemma 6 (i) and (ii), (2.30) and (2.31),
Rosser-Schoenfeld (3.3), Lemma 9 and Lemma 14, as the lab states them in P0032. -/
theorem statement27_of_RV (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33) (h9 : Lemma9P)
    (h14 : Lemma14P) : Statement27 :=
  statement27_of_density26 (density26_of_density11
    (density11_of (lemma7_of_RS hRS) (lemma8_of h24 h42 h278 h396 h6 hTab)
      (display91_of h9 h14 h6 h6')))

/-- The catalogue Prop `vaughan1977_stmt` of Statements.lean is `Statement27`. -/
theorem vaughan1977_stmt_iff : LeanLab.SchnirelmannBounds.vaughan1977_stmt ↔ Statement27 :=
  Iff.rfl

/-- **`vaughan1977_stmt`, CONDITIONAL ON** the same Riesel-Vaughan inputs. -/
theorem vaughan1977_of_RV (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33) (h9 : Lemma9P)
    (h14 : Lemma14P) : LeanLab.SchnirelmannBounds.vaughan1977_stmt :=
  statement27_of_RV h24 h42 h278 h396 h6 h6' hTab hRS h9 h14

/-- **`vaughan1977_stmt`, CONDITIONAL ON** the reconstructed input `VaughanDensity26`. -/
theorem vaughan1977_of_density26 (h : VaughanDensity26) :
    LeanLab.SchnirelmannBounds.vaughan1977_stmt :=
  statement27_of_density26 h

end LeanLab.SchnirelmannBounds.Vaughan1977
