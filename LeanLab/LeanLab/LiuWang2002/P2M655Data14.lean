/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_14.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/eb9e1cd5-8c46-4b36-9abe-b67294ece1a2
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData14.s0 : Seg := ⟨236910301832165443549579431, 236910301832165448042213863, 12845059, 65536, [], 239312716629432030222531846, 239312716629432034760722903⟩
def PrimData14.s1 : Seg := ⟨239312716629432030222531846, 239312716629432034760722903, 12976131, 65536, [], 241710267446006960569313133, 241710267446006965152972898⟩
def PrimData14.s2 : Seg := ⟨241710267446006960569313133, 241710267446006965152972898, 13107203, 65536, [], 244130755095105200998707347, 244130755095105205628253931⟩
def PrimData14.s3 : Seg := ⟨244130755095105200998707347, 244130755095105205628253931, 13238275, 65536, [], 246551193335702619516260590, 246551193335702624191713857⟩
def PrimData14.s4 : Seg := ⟨246551193335702619516260590, 246551193335702624191713857, 13369347, 65536, [], 248951275694715984081758056, 248951275694715988802734188⟩
def PrimData14.s5 : Seg := ⟨248951275694715984081758056, 248951275694715988802734188, 13500419, 65536, [], 251369139466159190563625856, 251369139466159195330444290⟩
def PrimData14.s6 : Seg := ⟨251369139466159190563625856, 251369139466159195330444290, 13631491, 65536, [], 253792657888517438611597777, 253792657888517443424373437⟩

def PrimData14.segs : List Seg := [PrimData14.s0, PrimData14.s1, PrimData14.s2, PrimData14.s3, PrimData14.s4, PrimData14.s5, PrimData14.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked14_s0 : Seg.bok PrimData14.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked14_s0

theorem checked14_s1 : Seg.bok PrimData14.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked14_s1

theorem checked14_s2 : Seg.bok PrimData14.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked14_s2

theorem checked14_s3 : Seg.bok PrimData14.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked14_s3

theorem checked14_s4 : Seg.bok PrimData14.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked14_s4

theorem checked14_s5 : Seg.bok PrimData14.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked14_s5

theorem checked14_s6 : Seg.bok PrimData14.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked14_s6

 theorem checked14 : ∀ s ∈ PrimData14.segs, (Seg.bok s) = true := by
  unfold PrimData14.segs
  exact List.forall_mem_cons.2 ⟨checked14_s0, List.forall_mem_cons.2 ⟨checked14_s1, List.forall_mem_cons.2 ⟨checked14_s2, List.forall_mem_cons.2 ⟨checked14_s3, List.forall_mem_cons.2 ⟨checked14_s4, List.forall_mem_cons.2 ⟨checked14_s5, List.forall_mem_singleton.2 checked14_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked14
