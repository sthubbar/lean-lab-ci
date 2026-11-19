/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_3.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/ed13cdef-3a0c-45c5-804a-e6ff19573be5
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData3.s0 : Seg := ⟨50738232456578986518095520, 50738232456578987480247599, 2752515, 65536, [], 53161684059256615497480866, 53161684059256616505593446⟩
def PrimData3.s1 : Seg := ⟨53161684059256615497480866, 53161684059256616505593446, 2883587, 65536, [], 55578008038011208461481239, 55578008038011209515416353⟩
def PrimData3.s2 : Seg := ⟨55578008038011208461481239, 55578008038011209515416353, 3014659, 65536, [], 57987332130655336215833865, 57987332130655337315452819⟩
def PrimData3.s3 : Seg := ⟨57987332130655336215833865, 57987332130655337315452819, 3145731, 65536, [], 60425194394908542390021863, 60425194394908543535871891⟩
def PrimData3.s4 : Seg := ⟨60425194394908542390021863, 60425194394908543535871891, 3276803, 65536, [], 62835771753263751908213555, 62835771753263753099774316⟩
def PrimData3.s5 : Seg := ⟨62835771753263751908213555, 62835771753263753099774316, 3407875, 65536, [], 65229992208343803034378498, 65229992208343804271342794⟩
def PrimData3.s6 : Seg := ⟨65229992208343803034378498, 65229992208343804271342794, 3538947, 65536, [], 67650450518408628219751483, 67650450518408629502617226⟩

def PrimData3.segs : List Seg := [PrimData3.s0, PrimData3.s1, PrimData3.s2, PrimData3.s3, PrimData3.s4, PrimData3.s5, PrimData3.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked03_s0 : Seg.bok PrimData3.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked03_s0

theorem checked03_s1 : Seg.bok PrimData3.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked03_s1

theorem checked03_s2 : Seg.bok PrimData3.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked03_s2

theorem checked03_s3 : Seg.bok PrimData3.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked03_s3

theorem checked03_s4 : Seg.bok PrimData3.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked03_s4

theorem checked03_s5 : Seg.bok PrimData3.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked03_s5

theorem checked03_s6 : Seg.bok PrimData3.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked03_s6

 theorem checked03 : ∀ s ∈ PrimData3.segs, (Seg.bok s) = true := by
  unfold PrimData3.segs
  exact List.forall_mem_cons.2 ⟨checked03_s0, List.forall_mem_cons.2 ⟨checked03_s1, List.forall_mem_cons.2 ⟨checked03_s2, List.forall_mem_cons.2 ⟨checked03_s3, List.forall_mem_cons.2 ⟨checked03_s4, List.forall_mem_cons.2 ⟨checked03_s5, List.forall_mem_singleton.2 checked03_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked03
