/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_74.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/b6a8a5fb-477c-4368-bcf8-303b349d96f3
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData74.s0 : Seg := ⟨588650822501545982291308738, 588650822501545993454285301, 31916035, 4096, [], 588808915892863270210610037, 588808915892863281376585336⟩
def PrimData74.s1 : Seg := ⟨588808915892863270210610037, 588808915892863281376585336, 31924227, 4096, [], 588950437066798574147706504, 588950437066798585316364639⟩
def PrimData74.s2 : Seg := ⟨588950437066798574147706504, 588950437066798585316364639, 31932419, 4096, [], 589104072706579258253880021, 589104072706579269425451625⟩
def PrimData74.s3 : Seg := ⟨589104072706579258253880021, 589104072706579269425451625, 31940611, 4096, [], 589253248105701470293616492, 589253248105701481468016732⟩
def PrimData74.s4 : Seg := ⟨589253248105701470293616492, 589253248105701481468016732, 31948803, 4096, [], 589405931984106661904097662, 589405931984106673081393152⟩
def PrimData74.s5 : Seg := ⟨589405931984106661904097662, 589405931984106673081393152, 31956995, 4096, [], 589560849507196319503301138, 589560849507196330683534614⟩
def PrimData74.s6 : Seg := ⟨589560849507196319503301138, 589560849507196330683534614, 31965187, 4096, [], 589711306625830136457413525, 589711306625830147640499941⟩
def PrimData74.s7 : Seg := ⟨589711306625830136457413525, 589711306625830147640499941, 31973379, 4096, [], 589862403438163080081098099, 589862403438163091267049601⟩
def PrimData74.s8 : Seg := ⟨589862403438163080081098099, 589862403438163091267049601, 31981571, 4096, [], 590009996037381518942999867, 590009996037381530131749630⟩
def PrimData74.s9 : Seg := ⟨590009996037381518942999867, 590009996037381530131749630, 31989763, 4096, [], 590161097331805356967569302, 590161097331805368159184151⟩
def PrimData74.s10 : Seg := ⟨590161097331805356967569302, 590161097331805368159184151, 31997955, 4096, [], 590315707487913136229663588, 590315707487913147424210348⟩

def PrimData74.segs : List Seg := [PrimData74.s0, PrimData74.s1, PrimData74.s2, PrimData74.s3, PrimData74.s4, PrimData74.s5, PrimData74.s6, PrimData74.s7, PrimData74.s8, PrimData74.s9, PrimData74.s10]

end ThetaSieve


namespace ThetaSieve
theorem checked74_s0 : Seg.bok PrimData74.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74_s0

theorem checked74_s1 : Seg.bok PrimData74.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74_s1

theorem checked74_s2 : Seg.bok PrimData74.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74_s2

theorem checked74_s3 : Seg.bok PrimData74.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74_s3

theorem checked74_s4 : Seg.bok PrimData74.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74_s4

theorem checked74_s5 : Seg.bok PrimData74.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74_s5

theorem checked74_s6 : Seg.bok PrimData74.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74_s6

theorem checked74_s7 : Seg.bok PrimData74.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74_s7

theorem checked74_s8 : Seg.bok PrimData74.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74_s8

theorem checked74_s9 : Seg.bok PrimData74.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74_s9

theorem checked74_s10 : Seg.bok PrimData74.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74_s10

 theorem checked74 : ∀ s ∈ PrimData74.segs, (Seg.bok s) = true := by
  unfold PrimData74.segs
  exact List.forall_mem_cons.2 ⟨checked74_s0, List.forall_mem_cons.2 ⟨checked74_s1, List.forall_mem_cons.2 ⟨checked74_s2, List.forall_mem_cons.2 ⟨checked74_s3, List.forall_mem_cons.2 ⟨checked74_s4, List.forall_mem_cons.2 ⟨checked74_s5, List.forall_mem_cons.2 ⟨checked74_s6, List.forall_mem_cons.2 ⟨checked74_s7, List.forall_mem_cons.2 ⟨checked74_s8, List.forall_mem_cons.2 ⟨checked74_s9, List.forall_mem_singleton.2 checked74_s10⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked74
