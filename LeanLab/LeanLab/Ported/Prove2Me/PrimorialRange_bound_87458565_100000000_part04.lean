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

theorem segment_16 :
    primSeg 18458400208034708012 87458565 91652869 16 8192 1690523289902527986314244128 = some 1695346669093799802655779858 := by
  decide +kernel

theorem segment_17 :
    primSeg 18458400208034708012 87458565 91915013 16 8192 1695346669093799802655779858 = some 1700186021723127277279442119 := by
  decide +kernel

theorem segment_18 :
    primSeg 18458400208034708012 87458565 92177157 16 8192 1700186021723127277279442119 = some 1705003118578450943913422861 := by
  decide +kernel

theorem segment_19 :
    primSeg 18458400208034708012 87458565 92439301 16 8192 1705003118578450943913422861 = some 1709854122000694116892769147 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_16
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_17
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_18
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_19
