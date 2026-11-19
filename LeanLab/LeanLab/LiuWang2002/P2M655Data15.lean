/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_15.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/6c92dcdc-9079-4c71-8723-372f538a5425
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData15.s0 : Seg := ⟨253792657888517438611597777, 253792657888517443424373437, 13762563, 65536, [], 256222132547694801117888667, 256222132547694805976741875⟩
def PrimData15.s1 : Seg := ⟨256222132547694801117888667, 256222132547694805976741875, 13893635, 65536, [], 258626898684251602065807599, 258626898684251606970254679⟩
def PrimData15.s2 : Seg := ⟨258626898684251602065807599, 258626898684251606970254679, 14024707, 65536, [], 261050343241663287890948370, 261050343241663292841358921⟩
def PrimData15.s3 : Seg := ⟨261050343241663287890948370, 261050343241663292841358921, 14155779, 65536, [], 263463608930514876366168616, 263463608930514881362341286⟩
def PrimData15.s4 : Seg := ⟨263463608930514876366168616, 263463608930514881362341286, 14286851, 65536, [], 265900406756592353358761652, 265900406756592358401142955⟩
def PrimData15.s5 : Seg := ⟨265900406756592353358761652, 265900406756592358401142955, 14417923, 65536, [], 268304786602973146261293720, 268304786602973151349265305⟩
def PrimData15.s6 : Seg := ⟨268304786602973146261293720, 268304786602973151349265305, 14548995, 65536, [], 270719303875204127302884649, 270719303875204132436649856⟩

def PrimData15.segs : List Seg := [PrimData15.s0, PrimData15.s1, PrimData15.s2, PrimData15.s3, PrimData15.s4, PrimData15.s5, PrimData15.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked15_s0 : Seg.bok PrimData15.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked15_s0

theorem checked15_s1 : Seg.bok PrimData15.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked15_s1

theorem checked15_s2 : Seg.bok PrimData15.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked15_s2

theorem checked15_s3 : Seg.bok PrimData15.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked15_s3

theorem checked15_s4 : Seg.bok PrimData15.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked15_s4

theorem checked15_s5 : Seg.bok PrimData15.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked15_s5

theorem checked15_s6 : Seg.bok PrimData15.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked15_s6

 theorem checked15 : ∀ s ∈ PrimData15.segs, (Seg.bok s) = true := by
  unfold PrimData15.segs
  exact List.forall_mem_cons.2 ⟨checked15_s0, List.forall_mem_cons.2 ⟨checked15_s1, List.forall_mem_cons.2 ⟨checked15_s2, List.forall_mem_cons.2 ⟨checked15_s3, List.forall_mem_cons.2 ⟨checked15_s4, List.forall_mem_cons.2 ⟨checked15_s5, List.forall_mem_singleton.2 checked15_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked15
