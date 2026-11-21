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

theorem segment_36 :
    primSeg 18458400208034708012 87458565 96895749 16 8192 1787233997955986757474970567 = some 1792077756486736510820171354 := by
  decide +kernel

theorem segment_37 :
    primSeg 18458400208034708012 87458565 97157893 16 8192 1792077756486736510820171354 = some 1796897799109876839830376406 := by
  decide +kernel

theorem segment_38 :
    primSeg 18458400208034708012 87458565 97420037 16 8192 1796897799109876839830376406 = some 1801765373164736099671943276 := by
  decide +kernel

theorem segment_39 :
    primSeg 18458400208034708012 87458565 97682181 16 8192 1801765373164736099671943276 = some 1806628907993089694093532306 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_36
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_37
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_38
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_39
