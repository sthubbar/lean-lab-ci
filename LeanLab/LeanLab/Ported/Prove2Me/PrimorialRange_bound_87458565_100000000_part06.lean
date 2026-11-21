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

theorem segment_24 :
    primSeg 18458400208034708012 87458565 93750021 16 8192 1729157943243596354510256841 = some 1733997425434062979550754397 := by
  decide +kernel

theorem segment_25 :
    primSeg 18458400208034708012 87458565 94012165 16 8192 1733997425434062979550754397 = some 1738843059295462422260356919 := by
  decide +kernel

theorem segment_26 :
    primSeg 18458400208034708012 87458565 94274309 16 8192 1738843059295462422260356919 = some 1743684687528058284444237600 := by
  decide +kernel

theorem segment_27 :
    primSeg 18458400208034708012 87458565 94536453 16 8192 1743684687528058284444237600 = some 1748515189124496324068392399 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_24
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_25
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_26
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_27
