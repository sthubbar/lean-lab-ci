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

theorem segment_28 :
    primSeg 18458400208034708012 87458565 94798597 16 8192 1748515189124496324068392399 = some 1753394530806756428819951929 := by
  decide +kernel

theorem segment_29 :
    primSeg 18458400208034708012 87458565 95060741 16 8192 1753394530806756428819951929 = some 1758226484914574222878435750 := by
  decide +kernel

theorem segment_30 :
    primSeg 18458400208034708012 87458565 95322885 16 8192 1758226484914574222878435750 = some 1763085599909431739512712599 := by
  decide +kernel

theorem segment_31 :
    primSeg 18458400208034708012 87458565 95585029 16 8192 1763085599909431739512712599 = some 1767895947969011449781759099 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_28
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_29
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_30
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_31
