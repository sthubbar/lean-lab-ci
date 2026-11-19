/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_7.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/86128b0d-b3eb-4944-a4bd-9dd50d3e337b
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData7.s0 : Seg := ⟨118412439619807149468598397, 118412439619807151714097600, 6422531, 65536, [], 120826452434641554040032508, 120826452434641556331312073⟩
def PrimData7.s1 : Seg := ⟨120826452434641554040032508, 120826452434641556331312073, 6553603, 65536, [], 123241505414815725288022745, 123241505414815727625092666⟩
def PrimData7.s2 : Seg := ⟨123241505414815725288022745, 123241505414815727625092666, 6684675, 65536, [], 125667409074356355135699740, 125667409074356357518775519⟩
def PrimData7.s3 : Seg := ⟨125667409074356355135699740, 125667409074356357518775519, 6815747, 65536, [], 128097441488274497983725029, 128097441488274500412887617⟩
def PrimData7.s4 : Seg := ⟨128097441488274497983725029, 128097441488274500412887617, 6946819, 65536, [], 130530387950041754343014340, 130530387950041756818309884⟩
def PrimData7.s5 : Seg := ⟨130530387950041754343014340, 130530387950041756818309884, 7077891, 65536, [], 132938537417078736970844395, 132938537417078739491805799⟩
def PrimData7.s6 : Seg := ⟨132938537417078736970844395, 132938537417078739491805799, 7208963, 65536, [], 135354997734773423294873595, 135354997734773425861660085⟩

def PrimData7.segs : List Seg := [PrimData7.s0, PrimData7.s1, PrimData7.s2, PrimData7.s3, PrimData7.s4, PrimData7.s5, PrimData7.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked07_s0 : Seg.bok PrimData7.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked07_s0

theorem checked07_s1 : Seg.bok PrimData7.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked07_s1

theorem checked07_s2 : Seg.bok PrimData7.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked07_s2

theorem checked07_s3 : Seg.bok PrimData7.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked07_s3

theorem checked07_s4 : Seg.bok PrimData7.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked07_s4

theorem checked07_s5 : Seg.bok PrimData7.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked07_s5

theorem checked07_s6 : Seg.bok PrimData7.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked07_s6

 theorem checked07 : ∀ s ∈ PrimData7.segs, (Seg.bok s) = true := by
  unfold PrimData7.segs
  exact List.forall_mem_cons.2 ⟨checked07_s0, List.forall_mem_cons.2 ⟨checked07_s1, List.forall_mem_cons.2 ⟨checked07_s2, List.forall_mem_cons.2 ⟨checked07_s3, List.forall_mem_cons.2 ⟨checked07_s4, List.forall_mem_cons.2 ⟨checked07_s5, List.forall_mem_singleton.2 checked07_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked07
