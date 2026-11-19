/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_12.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/e889c6ba-3838-490c-85f2-d1b0989b4a5e
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData12.s0 : Seg := ⟨203032315976804453386836300, 203032315976804457237019916, 11010051, 65536, [], 205448440103465702187313960, 205448440103465706083318134⟩
def PrimData12.s1 : Seg := ⟨205448440103465702187313960, 205448440103465706083318134, 11141123, 65536, [], 207869308170523395798070436, 207869308170523399739972907⟩
def PrimData12.s2 : Seg := ⟨207869308170523395798070436, 207869308170523399739972907, 11272195, 65536, [], 210279929765540840726699684, 210279929765540844714319291⟩
def PrimData12.s3 : Seg := ⟨210279929765540840726699684, 210279929765540844714319291, 11403267, 65536, [], 212699155407097362506425241, 212699155407097366539934748⟩
def PrimData12.s4 : Seg := ⟨212699155407097362506425241, 212699155407097366539934748, 11534339, 65536, [], 215133571593409791258263660, 215133571593409795337934868⟩
def PrimData12.s5 : Seg := ⟨215133571593409791258263660, 215133571593409795337934868, 11665411, 65536, [], 217546251890993418985295791, 217546251890993423110689523⟩
def PrimData12.s6 : Seg := ⟨217546251890993418985295791, 217546251890993423110689523, 11796483, 65536, [], 219970796465872430687379675, 219970796465872434858773145⟩

def PrimData12.segs : List Seg := [PrimData12.s0, PrimData12.s1, PrimData12.s2, PrimData12.s3, PrimData12.s4, PrimData12.s5, PrimData12.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked12_s0 : Seg.bok PrimData12.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked12_s0

theorem checked12_s1 : Seg.bok PrimData12.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked12_s1

theorem checked12_s2 : Seg.bok PrimData12.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked12_s2

theorem checked12_s3 : Seg.bok PrimData12.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked12_s3

theorem checked12_s4 : Seg.bok PrimData12.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked12_s4

theorem checked12_s5 : Seg.bok PrimData12.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked12_s5

theorem checked12_s6 : Seg.bok PrimData12.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked12_s6

 theorem checked12 : ∀ s ∈ PrimData12.segs, (Seg.bok s) = true := by
  unfold PrimData12.segs
  exact List.forall_mem_cons.2 ⟨checked12_s0, List.forall_mem_cons.2 ⟨checked12_s1, List.forall_mem_cons.2 ⟨checked12_s2, List.forall_mem_cons.2 ⟨checked12_s3, List.forall_mem_cons.2 ⟨checked12_s4, List.forall_mem_cons.2 ⟨checked12_s5, List.forall_mem_singleton.2 checked12_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked12
