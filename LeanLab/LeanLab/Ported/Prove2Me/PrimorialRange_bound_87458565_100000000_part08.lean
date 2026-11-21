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

theorem segment_32 :
    primSeg 18458400208034708012 87458565 95847173 16 8192 1767895947969011449781759099 = some 1772738201301046721716026658 := by
  decide +kernel

theorem segment_33 :
    primSeg 18458400208034708012 87458565 96109317 16 8192 1772738201301046721716026658 = some 1777553707603255946715879125 := by
  decide +kernel

theorem segment_34 :
    primSeg 18458400208034708012 87458565 96371461 16 8192 1777553707603255946715879125 = some 1782404519897945325739396542 := by
  decide +kernel

theorem segment_35 :
    primSeg 18458400208034708012 87458565 96633605 16 8192 1782404519897945325739396542 = some 1787233997955986757474970567 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_32
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_33
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_34
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_35
