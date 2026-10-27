import LeanLab.Halupczok2012.U1495PPS
import LeanLab.Halupczok2012.U1496PP

/-!
# P0077 Halupczok 2012, unit U-1510, run 20261025T0416Z-19415

AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

The final form of the F-0008 repair of Halupczok's Theorem 2, arXiv 1212.4406 Theorem 2,
JTNB 25 2013 Theorem 1.2 pp. 333-334, page image checked in U-1510.

It rests on exactly two cited inputs, both checked against page images:

* `PPS1984Remark`: the printed REMARK of Perelli-Pintz-Salerno 1984, Ann. SNS Pisa 11, p. 530,
  with display (2) of p. 529, in its uniform reading; U-1510 read the proof pp. 531-538 and found
  the only theta dependence is `delta = delta(theta)` in display (5) p. 531, which can be taken
  absolute; see PROGRESS.md, U-1510.
* `PP1993Goldbach`: the unnumbered Goldbach analogue of Perelli-Pintz 1993 Theorem 3,
  J. London Math. Soc. 47 pp. 44-46, displays (1), (3), (4), (5). It replaces Halupczok's
  Theorem 2.3, JTNB p. 339, which the paper itself calls an adaptation of [11].

No `sorry` is used; `Statements.lean` sorries are not in the import path of these proofs'
axioms, as `#print axioms` below shows.
-/

namespace LeanLab.Halupczok2012

/-- The F-0008 repair, all `q ≤ Q` with `T0`, CONDITIONAL ON `PPS1984Remark` and
`PP1993Goldbach`. -/
theorem theorem2Zeroed_U1510 (hR : PPS1984Remark) (hPP : PP1993Goldbach) :
    Theorem2Zeroed :=
  theorem2Zeroed_U1496 (theorem3_of_uniform (uniform_of_remark hR)) hPP

/-- Theorem 2 in the coprime reading, CONDITIONAL ON `PPS1984Remark` and `PP1993Goldbach`. -/
theorem theorem2_U1510 (hR : PPS1984Remark) (hPP : PP1993Goldbach) : Theorem2 :=
  theorem2_U1496 (theorem3_of_uniform (uniform_of_remark hR)) hPP

/-- The paper's own quoted Theorem 2.1, the lab's `Theorem3`, follows from the printed Remark. -/
theorem theorem3_of_remark (hR : PPS1984Remark) : Theorem3 :=
  theorem3_of_uniform (uniform_of_remark hR)

/-- The paper's own Theorem 2.3, the lab's `Theorem5`, follows from `PP1993Goldbach`. -/
theorem theorem5_of_PP1993 (hPP : PP1993Goldbach) : Theorem5 :=
  theorem5_of_PP hPP

end LeanLab.Halupczok2012

#print axioms LeanLab.Halupczok2012.theorem2Zeroed_U1510
#print axioms LeanLab.Halupczok2012.theorem2_U1510
#print axioms LeanLab.Halupczok2012.theorem3_of_remark
#print axioms LeanLab.Halupczok2012.theorem5_of_PP1993
#print axioms LeanLab.Halupczok2012.theorem2Zeroed_U1462
#print axioms LeanLab.Halupczok2012.theorem2_U1462
