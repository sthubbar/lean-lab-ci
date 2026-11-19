/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_6.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/817013b5-ee64-4c2b-8115-7a2125b1e2f3
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData6.s0 : Seg := ⟨101512749294931043246950046, 101512749294931045171972978, 5505027, 65536, [], 103919629605615013315204983, 103919629605615015285868141⟩
def PrimData6.s1 : Seg := ⟨103919629605615013315204983, 103919629605615015285868141, 5636099, 65536, [], 106328391098867353953433708, 106328391098867355969781740⟩
def PrimData6.s2 : Seg := ⟨106328391098867353953433708, 106328391098867355969781740, 5767171, 65536, [], 108744700358953986479134209, 108744700358953988541285792⟩
def PrimData6.s3 : Seg := ⟨108744700358953986479134209, 108744700358953988541285792, 5898243, 65536, [], 111178262321727320329815162, 111178262321727322438137925⟩
def PrimData6.s4 : Seg := ⟨111178262321727320329815162, 111178262321727322438137925, 6029315, 65536, [], 113584100717406891517601964, 113584100717406893671536908⟩
def PrimData6.s5 : Seg := ⟨113584100717406891517601964, 113584100717406893671536908, 6160387, 65536, [], 116003312656943163476025464, 116003312656943165675838242⟩
def PrimData6.s6 : Seg := ⟨116003312656943163476025464, 116003312656943165675838242, 6291459, 65536, [], 118412439619807149468598397, 118412439619807151714097600⟩

def PrimData6.segs : List Seg := [PrimData6.s0, PrimData6.s1, PrimData6.s2, PrimData6.s3, PrimData6.s4, PrimData6.s5, PrimData6.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked06_s0 : Seg.bok PrimData6.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked06_s0

theorem checked06_s1 : Seg.bok PrimData6.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked06_s1

theorem checked06_s2 : Seg.bok PrimData6.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked06_s2

theorem checked06_s3 : Seg.bok PrimData6.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked06_s3

theorem checked06_s4 : Seg.bok PrimData6.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked06_s4

theorem checked06_s5 : Seg.bok PrimData6.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked06_s5

theorem checked06_s6 : Seg.bok PrimData6.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked06_s6

 theorem checked06 : ∀ s ∈ PrimData6.segs, (Seg.bok s) = true := by
  unfold PrimData6.segs
  exact List.forall_mem_cons.2 ⟨checked06_s0, List.forall_mem_cons.2 ⟨checked06_s1, List.forall_mem_cons.2 ⟨checked06_s2, List.forall_mem_cons.2 ⟨checked06_s3, List.forall_mem_cons.2 ⟨checked06_s4, List.forall_mem_cons.2 ⟨checked06_s5, List.forall_mem_singleton.2 checked06_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked06
