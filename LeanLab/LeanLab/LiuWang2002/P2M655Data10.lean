/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_10.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/6fc6b2b0-e286-4a68-a3e7-e99a600daa5b
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData10.s0 : Seg := ⟨169182264143941766940464450, 169182264143941770148717453, 9175043, 65536, [], 171615786220914218834980278, 171615786220914222089392538⟩
def PrimData10.s1 : Seg := ⟨171615786220914218834980278, 171615786220914222089392538, 9306115, 65536, [], 174022424540493076441276828, 174022424540493079741334871⟩
def PrimData10.s2 : Seg := ⟨174022424540493076441276828, 174022424540493079741334871, 9437187, 65536, [], 176433221601052817754443581, 176433221601052821100222165⟩
def PrimData10.s3 : Seg := ⟨176433221601052817754443581, 176433221601052821100222165, 9568259, 65536, [], 178861196218641360375191030, 178861196218641363767012557⟩
def PrimData10.s4 : Seg := ⟨178861196218641360375191030, 178861196218641363767012557, 9699331, 65536, [], 181285282335047259891820462, 181285282335047263329611966⟩
def PrimData10.s5 : Seg := ⟨181285282335047259891820462, 181285282335047263329611966, 9830403, 65536, [], 183678989964445108978597099, 183678989964445112461770436⟩
def PrimData10.s6 : Seg := ⟨183678989964445108978597099, 183678989964445112461770436, 9961475, 65536, [], 186095470539918573924399197, 186095470539918577453405646⟩

def PrimData10.segs : List Seg := [PrimData10.s0, PrimData10.s1, PrimData10.s2, PrimData10.s3, PrimData10.s4, PrimData10.s5, PrimData10.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked10_s0 : Seg.bok PrimData10.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked10_s0

theorem checked10_s1 : Seg.bok PrimData10.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked10_s1

theorem checked10_s2 : Seg.bok PrimData10.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked10_s2

theorem checked10_s3 : Seg.bok PrimData10.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked10_s3

theorem checked10_s4 : Seg.bok PrimData10.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked10_s4

theorem checked10_s5 : Seg.bok PrimData10.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked10_s5

theorem checked10_s6 : Seg.bok PrimData10.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked10_s6

 theorem checked10 : ∀ s ∈ PrimData10.segs, (Seg.bok s) = true := by
  unfold PrimData10.segs
  exact List.forall_mem_cons.2 ⟨checked10_s0, List.forall_mem_cons.2 ⟨checked10_s1, List.forall_mem_cons.2 ⟨checked10_s2, List.forall_mem_cons.2 ⟨checked10_s3, List.forall_mem_cons.2 ⟨checked10_s4, List.forall_mem_cons.2 ⟨checked10_s5, List.forall_mem_singleton.2 checked10_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked10
