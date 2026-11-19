/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_5.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/f0f7c60e-2c20-493c-9011-7d45a43e2367
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData5.s0 : Seg := ⟨84580223118700218988344251, 84580223118700220592247921, 4587523, 65536, [], 86999713916019588196637348, 86999713916019589846429961⟩
def PrimData5.s1 : Seg := ⟨86999713916019588196637348, 86999713916019589846429961, 4718595, 65536, [], 89411381445387458623753359, 89411381445387460319283178⟩
def PrimData5.s2 : Seg := ⟨89411381445387458623753359, 89411381445387460319283178, 4849667, 65536, [], 91850593137441723421606632, 91850593137441725163394587⟩
def PrimData5.s3 : Seg := ⟨91850593137441723421606632, 91850593137441725163394587, 4980739, 65536, [], 94259518150970532083966902, 94259518150970533871437550⟩
def PrimData5.s4 : Seg := ⟨94259518150970532083966902, 94259518150970533871437550, 5111811, 65536, [], 96676439549777769961827976, 96676439549777771795135720⟩
def PrimData5.s5 : Seg := ⟨96676439549777769961827976, 96676439549777771795135720, 5242883, 65536, [], 99095263268148018839641850, 99095263268148020718821991⟩
def PrimData5.s6 : Seg := ⟨99095263268148018839641850, 99095263268148020718821991, 5373955, 65536, [], 101512749294931043246950046, 101512749294931045171972978⟩

def PrimData5.segs : List Seg := [PrimData5.s0, PrimData5.s1, PrimData5.s2, PrimData5.s3, PrimData5.s4, PrimData5.s5, PrimData5.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked05_s0 : Seg.bok PrimData5.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked05_s0

theorem checked05_s1 : Seg.bok PrimData5.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked05_s1

theorem checked05_s2 : Seg.bok PrimData5.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked05_s2

theorem checked05_s3 : Seg.bok PrimData5.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked05_s3

theorem checked05_s4 : Seg.bok PrimData5.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked05_s4

theorem checked05_s5 : Seg.bok PrimData5.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked05_s5

theorem checked05_s6 : Seg.bok PrimData5.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked05_s6

 theorem checked05 : ∀ s ∈ PrimData5.segs, (Seg.bok s) = true := by
  unfold PrimData5.segs
  exact List.forall_mem_cons.2 ⟨checked05_s0, List.forall_mem_cons.2 ⟨checked05_s1, List.forall_mem_cons.2 ⟨checked05_s2, List.forall_mem_cons.2 ⟨checked05_s3, List.forall_mem_cons.2 ⟨checked05_s4, List.forall_mem_cons.2 ⟨checked05_s5, List.forall_mem_singleton.2 checked05_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked05
