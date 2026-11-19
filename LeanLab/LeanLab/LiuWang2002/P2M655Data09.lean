/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_9.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/958eb11b-26bc-4d6b-a4c6-26a222710c23
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData9.s0 : Seg := ⟨152264165381893857302247230, 152264165381893860189653591, 8257539, 65536, [], 154680647531886150714662185, 154680647531886153647827089⟩
def PrimData9.s1 : Seg := ⟨154680647531886150714662185, 154680647531886153647827089, 8388611, 65536, [], 157094207329463570263616654, 157094207329463573242645533⟩
def PrimData9.s2 : Seg := ⟨157094207329463570263616654, 157094207329463573242645533, 8519683, 65536, [], 159525107241979406761091686, 159525107241979409786269579⟩
def PrimData9.s3 : Seg := ⟨159525107241979406761091686, 159525107241979409786269579, 8650755, 65536, [], 161956254715816744517052849, 161956254715816747588340678⟩
def PrimData9.s4 : Seg := ⟨161956254715816744517052849, 161956254715816747588340678, 8781827, 65536, [], 164360756294591755717098291, 164360756294591758833956293⟩
def PrimData9.s5 : Seg := ⟨164360756294591755717098291, 164360756294591758833956293, 8912899, 65536, [], 166768939607633126526734063, 166768939607633129689227944⟩
def PrimData9.s6 : Seg := ⟨166768939607633126526734063, 166768939607633129689227944, 9043971, 65536, [], 169182264143941766940464450, 169182264143941770148717453⟩

def PrimData9.segs : List Seg := [PrimData9.s0, PrimData9.s1, PrimData9.s2, PrimData9.s3, PrimData9.s4, PrimData9.s5, PrimData9.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked09_s0 : Seg.bok PrimData9.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked09_s0

theorem checked09_s1 : Seg.bok PrimData9.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked09_s1

theorem checked09_s2 : Seg.bok PrimData9.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked09_s2

theorem checked09_s3 : Seg.bok PrimData9.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked09_s3

theorem checked09_s4 : Seg.bok PrimData9.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked09_s4

theorem checked09_s5 : Seg.bok PrimData9.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked09_s5

theorem checked09_s6 : Seg.bok PrimData9.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked09_s6

 theorem checked09 : ∀ s ∈ PrimData9.segs, (Seg.bok s) = true := by
  unfold PrimData9.segs
  exact List.forall_mem_cons.2 ⟨checked09_s0, List.forall_mem_cons.2 ⟨checked09_s1, List.forall_mem_cons.2 ⟨checked09_s2, List.forall_mem_cons.2 ⟨checked09_s3, List.forall_mem_cons.2 ⟨checked09_s4, List.forall_mem_cons.2 ⟨checked09_s5, List.forall_mem_singleton.2 checked09_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked09
