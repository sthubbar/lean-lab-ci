/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_1.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/64bd3c9e-c1f6-4010-9d65-cf58f48be249
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData1.s0 : Seg := ⟨16906844048882945717223248, 16906844048882946037829117, 917507, 65536, [], 19319182800820645148719502, 19319182800820645515060685⟩
def PrimData1.s1 : Seg := ⟨19319182800820645148719502, 19319182800820645515060685, 1048579, 65536, [], 21743976388148939469412628, 21743976388148939881747051⟩
def PrimData1.s2 : Seg := ⟨21743976388148939469412628, 21743976388148939881747051, 1179651, 65536, [], 24156800680800159128796984, 24156800680800159586884419⟩
def PrimData1.s3 : Seg := ⟨24156800680800159128796984, 24156800680800159586884419, 1310723, 65536, [], 26573830403824655916006596, 26573830403824656419930748⟩
def PrimData1.s4 : Seg := ⟨26573830403824655916006596, 26573830403824656419930748, 1441795, 65536, [], 28991178078555431486694189, 28991178078555432036458855⟩
def PrimData1.s5 : Seg := ⟨28991178078555431486694189, 28991178078555432036458855, 1572867, 65536, [], 31405049667962231732432131, 31405049667962232327965867⟩
def PrimData1.s6 : Seg := ⟨31405049667962231732432131, 31405049667962232327965867, 1703939, 65536, [], 33822898766633561946684472, 33822898766633562588072272⟩

def PrimData1.segs : List Seg := [PrimData1.s0, PrimData1.s1, PrimData1.s2, PrimData1.s3, PrimData1.s4, PrimData1.s5, PrimData1.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked01_s0 : Seg.bok PrimData1.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked01_s0

theorem checked01_s1 : Seg.bok PrimData1.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked01_s1

theorem checked01_s2 : Seg.bok PrimData1.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked01_s2

theorem checked01_s3 : Seg.bok PrimData1.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked01_s3

theorem checked01_s4 : Seg.bok PrimData1.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked01_s4

theorem checked01_s5 : Seg.bok PrimData1.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked01_s5

theorem checked01_s6 : Seg.bok PrimData1.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked01_s6

 theorem checked01 : ∀ s ∈ PrimData1.segs, (Seg.bok s) = true := by
  unfold PrimData1.segs
  exact List.forall_mem_cons.2 ⟨checked01_s0, List.forall_mem_cons.2 ⟨checked01_s1, List.forall_mem_cons.2 ⟨checked01_s2, List.forall_mem_cons.2 ⟨checked01_s3, List.forall_mem_cons.2 ⟨checked01_s4, List.forall_mem_cons.2 ⟨checked01_s5, List.forall_mem_singleton.2 checked01_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked01
