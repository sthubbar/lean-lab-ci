/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_4.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/43957524-b960-456d-8056-3dc75db03cbf
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData4.s0 : Seg := ⟨67650450518408628219751483, 67650450518408629502617226, 3670019, 65536, [], 70072713753455044422230921, 70072713753455045751027845⟩
def PrimData4.s1 : Seg := ⟨70072713753455044422230921, 70072713753455045751027845, 3801091, 65536, [], 72501911950632555133565699, 72501911950632556508439696⟩
def PrimData4.s2 : Seg := ⟨72501911950632555133565699, 72501911950632556508439696, 3932163, 65536, [], 74915991793164034759567744, 74915991793164036180228738⟩
def PrimData4.s3 : Seg := ⟨74915991793164034759567744, 74915991793164036180228738, 4063235, 65536, [], 77332941354418201366188085, 77332941354418202832618782⟩
def PrimData4.s4 : Seg := ⟨77332941354418201366188085, 77332941354418202832618782, 4194307, 65536, [], 79733719058465780259125963, 79733719058465781771154064⟩
def PrimData4.s5 : Seg := ⟨79733719058465780259125963, 79733719058465781771154064, 4325379, 65536, [], 82163544925193353376923805, 82163544925193354935014378⟩
def PrimData4.s6 : Seg := ⟨82163544925193353376923805, 82163544925193354935014378, 4456451, 65536, [], 84580223118700218988344251, 84580223118700220592247921⟩

def PrimData4.segs : List Seg := [PrimData4.s0, PrimData4.s1, PrimData4.s2, PrimData4.s3, PrimData4.s4, PrimData4.s5, PrimData4.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked04_s0 : Seg.bok PrimData4.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked04_s0

theorem checked04_s1 : Seg.bok PrimData4.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked04_s1

theorem checked04_s2 : Seg.bok PrimData4.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked04_s2

theorem checked04_s3 : Seg.bok PrimData4.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked04_s3

theorem checked04_s4 : Seg.bok PrimData4.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked04_s4

theorem checked04_s5 : Seg.bok PrimData4.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked04_s5

theorem checked04_s6 : Seg.bok PrimData4.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked04_s6

 theorem checked04 : ∀ s ∈ PrimData4.segs, (Seg.bok s) = true := by
  unfold PrimData4.segs
  exact List.forall_mem_cons.2 ⟨checked04_s0, List.forall_mem_cons.2 ⟨checked04_s1, List.forall_mem_cons.2 ⟨checked04_s2, List.forall_mem_cons.2 ⟨checked04_s3, List.forall_mem_cons.2 ⟨checked04_s4, List.forall_mem_cons.2 ⟨checked04_s5, List.forall_mem_singleton.2 checked04_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked04
