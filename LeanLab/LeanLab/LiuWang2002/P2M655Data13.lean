/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_13.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/b5e069c3-8be6-48e9-800b-2c6adcdb3f46
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData13.s0 : Seg := ⟨219970796465872430687379675, 219970796465872434858773145, 11927555, 65536, [], 222386451081856408329755221, 222386451081856412546983020⟩
def PrimData13.s1 : Seg := ⟨222386451081856408329755221, 222386451081856412546983020, 12058627, 65536, [], 224795291833984484707633993, 224795291833984488970533957⟩
def PrimData13.s2 : Seg := ⟨224795291833984484707633993, 224795291833984488970533957, 12189699, 65536, [], 227228003362938141862661704, 227228003362938146171681165⟩
def PrimData13.s3 : Seg := ⟨227228003362938141862661704, 227228003362938146171681165, 12320771, 65536, [], 229651151250197576595100676, 229651151250197580950068508⟩
def PrimData13.s4 : Seg := ⟨229651151250197576595100676, 229651151250197580950068508, 12451843, 65536, [], 232053248961356556899444229, 232053248961356561299970405⟩
def PrimData13.s5 : Seg := ⟨232053248961356556899444229, 232053248961356561299970405, 12582915, 65536, [], 234477691864511484719940132, 234477691864511489166441349⟩
def PrimData13.s6 : Seg := ⟨234477691864511484719940132, 234477691864511489166441349, 12713987, 65536, [], 236910301832165443549579431, 236910301832165448042213863⟩

def PrimData13.segs : List Seg := [PrimData13.s0, PrimData13.s1, PrimData13.s2, PrimData13.s3, PrimData13.s4, PrimData13.s5, PrimData13.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked13_s0 : Seg.bok PrimData13.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked13_s0

theorem checked13_s1 : Seg.bok PrimData13.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked13_s1

theorem checked13_s2 : Seg.bok PrimData13.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked13_s2

theorem checked13_s3 : Seg.bok PrimData13.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked13_s3

theorem checked13_s4 : Seg.bok PrimData13.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked13_s4

theorem checked13_s5 : Seg.bok PrimData13.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked13_s5

theorem checked13_s6 : Seg.bok PrimData13.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked13_s6

 theorem checked13 : ∀ s ∈ PrimData13.segs, (Seg.bok s) = true := by
  unfold PrimData13.segs
  exact List.forall_mem_cons.2 ⟨checked13_s0, List.forall_mem_cons.2 ⟨checked13_s1, List.forall_mem_cons.2 ⟨checked13_s2, List.forall_mem_cons.2 ⟨checked13_s3, List.forall_mem_cons.2 ⟨checked13_s4, List.forall_mem_cons.2 ⟨checked13_s5, List.forall_mem_singleton.2 checked13_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked13
