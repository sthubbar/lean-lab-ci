/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_16.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/15d6fe5e-74f7-45f3-8183-e242803aa454
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData16.s0 : Seg := ⟨270719303875204127302884649, 270719303875204132436649856, 14680067, 65536, [], 273149745272316352743617984, 273149745272316357923474196⟩
def PrimData16.s1 : Seg := ⟨273149745272316352743617984, 273149745272316357923474196, 14811139, 65536, [], 275555898163550332730296315, 275555898163550337955772831⟩
def PrimData16.s2 : Seg := ⟨275555898163550332730296315, 275555898163550337955772831, 14942211, 65536, [], 277963329698894156704629001, 277963329698894161975758862⟩
def PrimData16.s3 : Seg := ⟨277963329698894156704629001, 277963329698894161975758862, 15073283, 65536, [], 280372635926705336518321671, 280372635926705341835135715⟩
def PrimData16.s4 : Seg := ⟨280372635926705336518321671, 280372635926705341835135715, 15204355, 65536, [], 282799981340096071390590375, 282799981340096076753432663⟩
def PrimData16.s5 : Seg := ⟨282799981340096071390590375, 282799981340096076753432663, 15335427, 65536, [], 285198359281014543449573717, 285198359281014548857910660⟩
def PrimData16.s6 : Seg := ⟨285198359281014543449573717, 285198359281014548857910660, 15466499, 65536, [], 287641951201008012394754886, 287641951201008017849453624⟩

def PrimData16.segs : List Seg := [PrimData16.s0, PrimData16.s1, PrimData16.s2, PrimData16.s3, PrimData16.s4, PrimData16.s5, PrimData16.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked16_s0 : Seg.bok PrimData16.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked16_s0

theorem checked16_s1 : Seg.bok PrimData16.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked16_s1

theorem checked16_s2 : Seg.bok PrimData16.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked16_s2

theorem checked16_s3 : Seg.bok PrimData16.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked16_s3

theorem checked16_s4 : Seg.bok PrimData16.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked16_s4

theorem checked16_s5 : Seg.bok PrimData16.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked16_s5

theorem checked16_s6 : Seg.bok PrimData16.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked16_s6

 theorem checked16 : ∀ s ∈ PrimData16.segs, (Seg.bok s) = true := by
  unfold PrimData16.segs
  exact List.forall_mem_cons.2 ⟨checked16_s0, List.forall_mem_cons.2 ⟨checked16_s1, List.forall_mem_cons.2 ⟨checked16_s2, List.forall_mem_cons.2 ⟨checked16_s3, List.forall_mem_cons.2 ⟨checked16_s4, List.forall_mem_cons.2 ⟨checked16_s5, List.forall_mem_singleton.2 checked16_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked16
