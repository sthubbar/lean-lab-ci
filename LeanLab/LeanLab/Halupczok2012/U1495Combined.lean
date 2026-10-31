import LeanLab.Halupczok2012.U1495PPS
import LeanLab.Halupczok2012.U1496PP

/-!
U-1495 main thread, run 20261022T2003Z-18. AI wrote this Lean code.
Combines U-1495 and U-1496: the F-0008 repair of Halupczok 2012 Theorem 2,
CONDITIONAL ON `PPS1984Uniform`, the printed Perelli-Pintz-Salerno 1984 theorem
with constants uniform in theta, implied by the printed Remark p. 530, and on
`PP1993Goldbach`, the unnumbered Goldbach analogue of Perelli-Pintz 1993 Theorem 3.
-/

namespace LeanLab.Halupczok2012

theorem theorem2Zeroed_U1495U1496 (hU : PPS1984Uniform) (hPP : PP1993Goldbach) :
    Theorem2Zeroed :=
  theorem2Zeroed_U1496 (theorem3_of_uniform hU) hPP

theorem theorem2_U1495U1496 (hU : PPS1984Uniform) (hPP : PP1993Goldbach) : Theorem2 :=
  theorem2_U1496 (theorem3_of_uniform hU) hPP

end LeanLab.Halupczok2012

#print axioms LeanLab.Halupczok2012.theorem2Zeroed_U1495U1496
#print axioms LeanLab.Halupczok2012.theorem2_U1495U1496
