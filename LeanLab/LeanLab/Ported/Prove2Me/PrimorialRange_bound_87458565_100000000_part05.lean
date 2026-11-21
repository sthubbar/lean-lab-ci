/-
Ported from Prove2Me, mission 0814790f.
Source PrimorialRange_bound_87458565_100000000. Author kmehltretter82. Apache 2.0.
Lean 4.33.1 source adapted for Lean 4.35.0.
Derived certificates for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ported.Prove2Me.LL_Decomp368b_primorial_c3

namespace LeanLab.Ported.Prove2Me.Task666.PrimC6R7
open LeanLab.Ported.Prove2Me.Task664.PrimC3Cert
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem segment_20 :
    primSeg 18458400208034708012 87458565 92701445 16 8192 1709854122000694116892769147 = some 1714695380829083728954359595 := by
  decide +kernel

theorem segment_21 :
    primSeg 18458400208034708012 87458565 92963589 16 8192 1714695380829083728954359595 = some 1719498122392544560375174667 := by
  decide +kernel

theorem segment_22 :
    primSeg 18458400208034708012 87458565 93225733 16 8192 1719498122392544560375174667 = some 1724348993426399085588701720 := by
  decide +kernel

theorem segment_23 :
    primSeg 18458400208034708012 87458565 93487877 16 8192 1724348993426399085588701720 = some 1729157943243596354510256841 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_20
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_21
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_22
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_23
