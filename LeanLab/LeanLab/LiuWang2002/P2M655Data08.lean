/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_8.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/a98814a4-014a-41e2-b538-b558872bcdcf
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData8.s0 : Seg := ⟨135354997734773423294873595, 135354997734773425861660085, 7340035, 65536, [], 137765435308109419192158125, 137765435308109421804650744⟩
def PrimData8.s1 : Seg := ⟨137765435308109419192158125, 137765435308109421804650744, 7471107, 65536, [], 140180011878570369917233443, 140180011878570372575510767⟩
def PrimData8.s2 : Seg := ⟨140180011878570369917233443, 140180011878570372575510767, 7602179, 65536, [], 142602183797691891829721139, 142602183797691894533934412⟩
def PrimData8.s3 : Seg := ⟨142602183797691891829721139, 142602183797691894533934412, 7733251, 65536, [], 145021394867239667344782493, 145021394867239670094898608⟩
def PrimData8.s4 : Seg := ⟨145021394867239667344782493, 145021394867239670094898608, 7864323, 65536, [], 147436398244268763413228786, 147436398244268766209164068⟩
def PrimData8.s5 : Seg := ⟨147436398244268763413228786, 147436398244268766209164068, 7995395, 65536, [], 149847444523602074207330966, 149847444523602077048970819⟩
def PrimData8.s6 : Seg := ⟨149847444523602074207330966, 149847444523602077048970819, 8126467, 65536, [], 152264165381893857302247230, 152264165381893860189653591⟩

def PrimData8.segs : List Seg := [PrimData8.s0, PrimData8.s1, PrimData8.s2, PrimData8.s3, PrimData8.s4, PrimData8.s5, PrimData8.s6]

end ThetaSieve


namespace ThetaSieve
theorem checked08_s0 : Seg.bok PrimData8.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked08_s0

theorem checked08_s1 : Seg.bok PrimData8.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked08_s1

theorem checked08_s2 : Seg.bok PrimData8.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked08_s2

theorem checked08_s3 : Seg.bok PrimData8.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked08_s3

theorem checked08_s4 : Seg.bok PrimData8.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked08_s4

theorem checked08_s5 : Seg.bok PrimData8.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked08_s5

theorem checked08_s6 : Seg.bok PrimData8.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked08_s6

 theorem checked08 : ∀ s ∈ PrimData8.segs, (Seg.bok s) = true := by
  unfold PrimData8.segs
  exact List.forall_mem_cons.2 ⟨checked08_s0, List.forall_mem_cons.2 ⟨checked08_s1, List.forall_mem_cons.2 ⟨checked08_s2, List.forall_mem_cons.2 ⟨checked08_s3, List.forall_mem_cons.2 ⟨checked08_s4, List.forall_mem_cons.2 ⟨checked08_s5, List.forall_mem_singleton.2 checked08_s6⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked08
