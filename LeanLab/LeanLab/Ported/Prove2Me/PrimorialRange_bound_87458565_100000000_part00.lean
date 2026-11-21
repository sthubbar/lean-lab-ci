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

theorem segment_00 :
    primSeg 18458400208034708012 87458565 87458565 16 8192 1613135228961610762836131252 = some 1617967895346841330083132101 := by
  decide +kernel

theorem segment_01 :
    primSeg 18458400208034708012 87458565 87720709 16 8192 1617967895346841330083132101 = some 1622815187480096358453008471 := by
  decide +kernel

theorem segment_02 :
    primSeg 18458400208034708012 87458565 87982853 16 8192 1622815187480096358453008471 = some 1627686891991475538761164172 := by
  decide +kernel

theorem segment_03 :
    primSeg 18458400208034708012 87458565 88244997 16 8192 1627686891991475538761164172 = some 1632508756646712378323668766 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_00
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_01
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_02
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_03
