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

theorem segment_44 :
    primSeg 18458400208034708012 87458565 98992901 16 8192 1825890459603517313306732144 = some 1830726263059863599359682889 := by
  decide +kernel

theorem segment_45 :
    primSeg 18458400208034708012 87458565 99255045 16 8192 1830726263059863599359682889 = some 1835553591653966124140131698 := by
  decide +kernel

theorem segment_46 :
    primSeg 18458400208034708012 87458565 99517189 16 8192 1835553591653966124140131698 = some 1840404031563309805502832600 := by
  decide +kernel

theorem segment_47 :
    primSeg 18458400208034708012 87458565 99779333 16 8192 1840404031563309805502832600 = some 1845241573501702431681285466 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_44
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_45
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_46
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_47
