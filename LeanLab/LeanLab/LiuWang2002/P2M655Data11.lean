/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_11.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/454aeaba-7d14-45d9-bf65-744bb73ba45b
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData11.s0 : Seg := ⟨186095470539918573924399197, 186095470539918577453405646, 10092547, 65536, [], 188498712590508733619659231, 188498712590508737194232504⟩
def PrimData11.s1 : Seg := ⟨188498712590508733619659231, 188498712590508737194232504, 10223619, 65536, [], 190917267665010052076437175, 190917267665010055696883783⟩
def PrimData11.s2 : Seg := ⟨190917267665010052076437175, 190917267665010055696883783, 10354691, 65536, [], 193352327785444209573839498, 193352327785444213240456887⟩
def PrimData11.s3 : Seg := ⟨193352327785444209573839498, 193352327785444213240456887, 10485763, 65536, [], 195771670431246400653466808, 195771670431246404365963840⟩
def PrimData11.s4 : Seg := ⟨195771670431246400653466808, 195771670431246404365963840, 10616835, 65536, [], 198204802176393046902501796, 198204802176393050661143475⟩
def PrimData11.s5 : Seg := ⟨198204802176393046902501796, 198204802176393050661143475, 10747907, 65536, [], 200612583163308556561675602, 200612583163308560365973194⟩
def PrimData11.s6 : Seg := ⟨200612583163308556561675602, 200612583163308560365973194, 10878979, 65536, [], 203032315976804453386836300, 203032315976804457237019916⟩

def PrimData11.segs : List Seg := [PrimData11.s0, PrimData11.s1, PrimData11.s2, PrimData11.s3, PrimData11.s4, PrimData11.s5, PrimData11.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked11_s0 : Seg.bok PrimData11.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked11_s0

theorem checked11_s1 : Seg.bok PrimData11.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked11_s1

theorem checked11_s2 : Seg.bok PrimData11.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked11_s2

theorem checked11_s3 : Seg.bok PrimData11.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked11_s3

theorem checked11_s4 : Seg.bok PrimData11.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked11_s4

theorem checked11_s5 : Seg.bok PrimData11.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked11_s5

theorem checked11_s6 : Seg.bok PrimData11.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked11_s6

 theorem checked11 : ∀ s ∈ PrimData11.segs, (Seg.bok s) = true := by
  unfold PrimData11.segs
  exact List.forall_mem_cons.2 ⟨checked11_s0, List.forall_mem_cons.2 ⟨checked11_s1, List.forall_mem_cons.2 ⟨checked11_s2, List.forall_mem_cons.2 ⟨checked11_s3, List.forall_mem_cons.2 ⟨checked11_s4, List.forall_mem_cons.2 ⟨checked11_s5, List.forall_mem_singleton.2 checked11_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked11
