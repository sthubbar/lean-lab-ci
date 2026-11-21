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

theorem segment_04 :
    primSeg 18458400208034708012 87458565 88507141 16 8192 1632508756646712378323668766 = some 1637321615013879641110348094 := by
  decide +kernel

theorem segment_05 :
    primSeg 18458400208034708012 87458565 88769285 16 8192 1637321615013879641110348094 = some 1642169009555752483696149544 := by
  decide +kernel

theorem segment_06 :
    primSeg 18458400208034708012 87458565 89031429 16 8192 1642169009555752483696149544 = some 1647037109518068167199852445 := by
  decide +kernel

theorem segment_07 :
    primSeg 18458400208034708012 87458565 89293573 16 8192 1647037109518068167199852445 = some 1651829660259314538149084677 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_04
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_05
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_06
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_07
