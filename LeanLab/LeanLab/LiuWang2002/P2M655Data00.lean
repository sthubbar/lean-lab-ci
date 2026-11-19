/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_0.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/d6c7e64b-a233-4384-b729-1e2941f1d46b
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData0.s0 : Seg := ⟨12786308645202655427, 12786308645202655670, 3, 65536, [], 2410511247392363703085771, 2410511247392363748796110⟩
def PrimData0.s1 : Seg := ⟨2410511247392363703085771, 2410511247392363748796110, 131075, 65536, [], 4822904977794544141515358, 4822904977794544232967787⟩
def PrimData0.s2 : Seg := ⟨4822904977794544141515358, 4822904977794544232967787, 262147, 65536, [], 7242583340656157963798969, 7242583340656158101140588⟩
def PrimData0.s3 : Seg := ⟨7242583340656157963798969, 7242583340656158101140588, 393219, 65536, [], 9659920023984658427163564, 9659920023984658610339780⟩
def PrimData0.s4 : Seg := ⟨9659920023984658427163564, 9659920023984658610339780, 524291, 65536, [], 12070909330197340498338073, 12070909330197340727238298⟩
def PrimData0.s5 : Seg := ⟨12070909330197340498338073, 12070909330197340727238298, 655363, 65536, [], 14488863649274660610409540, 14488863649274660885163672⟩
def PrimData0.s6 : Seg := ⟨14488863649274660610409540, 14488863649274660885163672, 786435, 65536, [], 16906844048882945717223248, 16906844048882946037829117⟩

def PrimData0.segs : List Seg := [PrimData0.s0, PrimData0.s1, PrimData0.s2, PrimData0.s3, PrimData0.s4, PrimData0.s5, PrimData0.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked00_s0 : Seg.bok PrimData0.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked00_s0

theorem checked00_s1 : Seg.bok PrimData0.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked00_s1

theorem checked00_s2 : Seg.bok PrimData0.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked00_s2

theorem checked00_s3 : Seg.bok PrimData0.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked00_s3

theorem checked00_s4 : Seg.bok PrimData0.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked00_s4

theorem checked00_s5 : Seg.bok PrimData0.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked00_s5

theorem checked00_s6 : Seg.bok PrimData0.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked00_s6

 theorem checked00 : ∀ s ∈ PrimData0.segs, (Seg.bok s) = true := by
  unfold PrimData0.segs
  exact List.forall_mem_cons.2 ⟨checked00_s0, List.forall_mem_cons.2 ⟨checked00_s1, List.forall_mem_cons.2 ⟨checked00_s2, List.forall_mem_cons.2 ⟨checked00_s3, List.forall_mem_cons.2 ⟨checked00_s4, List.forall_mem_cons.2 ⟨checked00_s5, List.forall_mem_singleton.2 checked00_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked00
