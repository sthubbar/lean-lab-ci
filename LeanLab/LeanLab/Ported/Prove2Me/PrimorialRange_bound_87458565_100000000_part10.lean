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

theorem segment_40 :
    primSeg 18458400208034708012 87458565 97944325 16 8192 1806628907993089694093532306 = some 1811423224979339720486176101 := by
  decide +kernel

theorem segment_41 :
    primSeg 18458400208034708012 87458565 98206469 16 8192 1811423224979339720486176101 = some 1816279006448653026088399328 := by
  decide +kernel

theorem segment_42 :
    primSeg 18458400208034708012 87458565 98468613 16 8192 1816279006448653026088399328 = some 1821107646535983409186423103 := by
  decide +kernel

theorem segment_43 :
    primSeg 18458400208034708012 87458565 98730757 16 8192 1821107646535983409186423103 = some 1825890459603517313306732144 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_40
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_41
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_42
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_43
