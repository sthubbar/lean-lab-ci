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

theorem segment_08 :
    primSeg 18458400208034708012 87458565 89555717 16 8192 1651829660259314538149084677 = some 1656612504182179557979974014 := by
  decide +kernel

theorem segment_09 :
    primSeg 18458400208034708012 87458565 89817861 16 8192 1656612504182179557979974014 = some 1661467060078554483910785350 := by
  decide +kernel

theorem segment_10 :
    primSeg 18458400208034708012 87458565 90080005 16 8192 1661467060078554483910785350 = some 1666338269248039251674950551 := by
  decide +kernel

theorem segment_11 :
    primSeg 18458400208034708012 87458565 90342149 16 8192 1666338269248039251674950551 = some 1671165300736204397273511076 := by
  decide +kernel

end LeanLab.Ported.Prove2Me.Task666.PrimC6R7
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_08
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_09
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_10
#print axioms LeanLab.Ported.Prove2Me.Task666.PrimC6R7.segment_11
