/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_17.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/e1c1500a-d130-4a23-bb5f-e061925fa7e8
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData17.s0 : Seg := ⟨287641951201008012394754886, 287641951201008017849453624, 15597571, 65536, [], 290054082194843772565053050, 290054082194843778065524075⟩
def PrimData17.s1 : Seg := ⟨290054082194843772565053050, 290054082194843778065524075, 15728643, 65536, [], 292478131132665993223673120, 292478131132665998770138892⟩

def PrimData17.segs : List Seg := [PrimData17.s0, PrimData17.s1]

end ThetaSieve


namespace ThetaSieve
theorem checked17_s0 : Seg.bok PrimData17.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked17_s0

theorem checked17_s1 : Seg.bok PrimData17.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked17_s1

 theorem checked17 : ∀ s ∈ PrimData17.segs, (Seg.bok s) = true := by
  unfold PrimData17.segs
  exact List.forall_mem_cons.2 ⟨checked17_s0, List.forall_mem_singleton.2 checked17_s1⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked17
