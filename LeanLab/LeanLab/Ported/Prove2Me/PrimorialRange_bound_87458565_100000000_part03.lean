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

theorem segment_12 :
    primSeg 18458400208034708012 87458565 90604293 16 8192 1671165300736204397273511076 = some 1675997827251520976803451924 := by
  decide +kernel

theorem segment_13 :
    primSeg 18458400208034708012 87458565 90866437 16 8192 1675997827251520976803451924 = some 1680833479885612446176124090 := by
  decide +kernel

theorem segment_14 :
    primSeg 18458400208034708012 87458565 91128581 16 8192 1680833479885612446176124090 = some 1685697279030829034098339296 := by
  decide +kernel

theorem segment_15 :
    primSeg 18458400208034708012 87458565 91390725 16 8192 1685697279030829034098339296 = some 1690523289902527986314244128 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_12
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_13
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_14
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_15
