/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_25.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/a6b9aa23-9650-49b2-a3d8-d1f79496b495
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData25.s0 : Seg := ⟨329517356150278026131463925, 329517356150278032380290523, 17866755, 4096, [], 329666753760993891485826039, 329666753760993897737484250⟩
def PrimData25.s1 : Seg := ⟨329666753760993891485826039, 329666753760993897737484250, 17874947, 4096, [], 329817387606574509340288981, 329817387606574515594801677⟩
def PrimData25.s2 : Seg := ⟨329817387606574509340288981, 329817387606574515594801677, 17883139, 4096, [], 329963096755667366023047162, 329963096755667372280320535⟩
def PrimData25.s3 : Seg := ⟨329963096755667366023047162, 329963096755667372280320535, 17891331, 4096, [], 330114971084863060429220672, 330114971084863066689372591⟩
def PrimData25.s4 : Seg := ⟨330114971084863060429220672, 330114971084863066689372591, 17899523, 4096, [], 330268081863069050531161217, 330268081863069056794214861⟩
def PrimData25.s5 : Seg := ⟨330268081863069050531161217, 330268081863069056794214861, 17907715, 4096, [], 330412570669408771478448972, 330412570669408777744240323⟩
def PrimData25.s6 : Seg := ⟨330412570669408771478448972, 330412570669408777744240323, 17915907, 4096, [], 330566922232549409233584413, 330566922232549415502300969⟩
def PrimData25.s7 : Seg := ⟨330566922232549409233584413, 330566922232549415502300969, 17924099, 4096, [], 330719737549118131224323650, 330719737549118137495935868⟩
def PrimData25.s8 : Seg := ⟨330719737549118131224323650, 330719737549118137495935868, 17932291, 4096, [], 330875021929946970724509762, 330875021929946976999064062⟩
def PrimData25.s9 : Seg := ⟨330875021929946970724509762, 330875021929946976999064062, 17940483, 4096, [], 331029078073503522014121216, 331029078073503528291594658⟩
def PrimData25.s10 : Seg := ⟨331029078073503522014121216, 331029078073503528291594658, 17948675, 4096, [], 331188068327764933126640937, 331188068327764939407127258⟩
def PrimData25.s11 : Seg := ⟨331188068327764933126640937, 331188068327764939407127258, 17956867, 4096, [], 331344289778285122364320800, 331344289778285128647768296⟩
def PrimData25.s12 : Seg := ⟨331344289778285122364320800, 331344289778285128647768296, 17965059, 4096, [], 331497125971396962212287126, 331497125971396968498631611⟩
def PrimData25.s13 : Seg := ⟨331497125971396962212287126, 331497125971396968498631611, 17973251, 4096, [], 331649966325664661881657838, 331649966325664668170899207⟩
def PrimData25.s14 : Seg := ⟨331649966325664661881657838, 331649966325664668170899207, 17981443, 4096, [], 331803735280898931196837131, 331803735280898937488993016⟩
def PrimData25.s15 : Seg := ⟨331803735280898931196837131, 331803735280898937488993016, 17989635, 4096, [], 331956892174610500138028773, 331956892174610506433088007⟩
def PrimData25.s16 : Seg := ⟨331956892174610500138028773, 331956892174610506433088007, 17997827, 4096, [], 332104197982241352938049606, 332104197982241359235900653⟩
def PrimData25.s17 : Seg := ⟨332104197982241352938049606, 332104197982241359235900653, 18006019, 4096, [], 332250275081765809587570029, 332250275081765815888189827⟩
def PrimData25.s18 : Seg := ⟨332250275081765809587570029, 332250275081765815888189827, 18014211, 4096, [], 332400978938280716708831291, 332400978938280723012306424⟩
def PrimData25.s19 : Seg := ⟨332400978938280716708831291, 332400978938280723012306424, 18022403, 4096, [], 332548296737614808439923393, 332548296737614814746189532⟩
def PrimData25.s20 : Seg := ⟨332548296737614808439923393, 332548296737614814746189532, 18030595, 4096, [], 332700241669730464913205607, 332700241669730471222352058⟩
def PrimData25.s21 : Seg := ⟨332700241669730464913205607, 332700241669730471222352058, 18038787, 4096, [], 332846334632104169807183493, 332846334632104176119097850⟩
def PrimData25.s22 : Seg := ⟨332846334632104169807183493, 332846334632104176119097850, 18046979, 4096, [], 332995513799752249012002714, 332995513799752255326743904⟩
def PrimData25.s23 : Seg := ⟨332995513799752249012002714, 332995513799752255326743904, 18055171, 4096, [], 333151786239031723687764454, 333151786239031730005467896⟩
def PrimData25.s24 : Seg := ⟨333151786239031723687764454, 333151786239031730005467896, 18063363, 4096, [], 333291109863038104565805475, 333291109863038110886148982⟩
def PrimData25.s25 : Seg := ⟨333291109863038104565805475, 333291109863038110886148982, 18071555, 4096, [], 333443691844296087124141645, 333443691844296093447377010⟩
def PrimData25.s26 : Seg := ⟨333443691844296087124141645, 333443691844296093447377010, 18079747, 4096, [], 333586105525266009715120050, 333586105525266016041053194⟩
def PrimData25.s27 : Seg := ⟨333586105525266009715120050, 333586105525266016041053194, 18087939, 4096, [], 333740237158571800500101320, 333740237158571806828955936⟩
def PrimData25.s28 : Seg := ⟨333740237158571800500101320, 333740237158571806828955936, 18096131, 4096, [], 333899613552400959812119644, 333899613552400966143995871⟩
def PrimData25.s29 : Seg := ⟨333899613552400959812119644, 333899613552400966143995871, 18104323, 4096, [], 334049129341193215950846606, 334049129341193222285556415⟩
def PrimData25.s30 : Seg := ⟨334049129341193215950846606, 334049129341193222285556415, 18112515, 4096, [], 334197724325790666537724898, 334197724325790672875251218⟩
def PrimData25.s31 : Seg := ⟨334197724325790666537724898, 334197724325790672875251218, 18120707, 4096, [], 334346939923580487165033129, 334346939923580493505388145⟩
def PrimData25.s32 : Seg := ⟨334346939923580487165033129, 334346939923580493505388145, 18128899, 4096, [], 334498317675943274160699481, 334498317675943280503923562⟩
def PrimData25.s33 : Seg := ⟨334498317675943274160699481, 334498317675943280503923562, 18137091, 4096, [], 334655865772443615268958987, 334655865772443621615170976⟩
def PrimData25.s34 : Seg := ⟨334655865772443615268958987, 334655865772443621615170976, 18145283, 4096, [], 334801085258342170523111720, 334801085258342176872076667⟩

def PrimData25.segs : List Seg := [PrimData25.s0, PrimData25.s1, PrimData25.s2, PrimData25.s3, PrimData25.s4, PrimData25.s5, PrimData25.s6, PrimData25.s7, PrimData25.s8, PrimData25.s9, PrimData25.s10, PrimData25.s11, PrimData25.s12, PrimData25.s13, PrimData25.s14, PrimData25.s15, PrimData25.s16, PrimData25.s17, PrimData25.s18, PrimData25.s19, PrimData25.s20, PrimData25.s21, PrimData25.s22, PrimData25.s23, PrimData25.s24, PrimData25.s25, PrimData25.s26, PrimData25.s27, PrimData25.s28, PrimData25.s29, PrimData25.s30, PrimData25.s31, PrimData25.s32, PrimData25.s33, PrimData25.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked25_s0 : Seg.bok PrimData25.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s0

theorem checked25_s1 : Seg.bok PrimData25.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s1

theorem checked25_s2 : Seg.bok PrimData25.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s2

theorem checked25_s3 : Seg.bok PrimData25.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s3

theorem checked25_s4 : Seg.bok PrimData25.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s4

theorem checked25_s5 : Seg.bok PrimData25.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s5

theorem checked25_s6 : Seg.bok PrimData25.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s6

theorem checked25_s7 : Seg.bok PrimData25.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s7

theorem checked25_s8 : Seg.bok PrimData25.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s8

theorem checked25_s9 : Seg.bok PrimData25.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s9

theorem checked25_s10 : Seg.bok PrimData25.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s10

theorem checked25_s11 : Seg.bok PrimData25.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s11

theorem checked25_s12 : Seg.bok PrimData25.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s12

theorem checked25_s13 : Seg.bok PrimData25.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s13

theorem checked25_s14 : Seg.bok PrimData25.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s14

theorem checked25_s15 : Seg.bok PrimData25.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s15

theorem checked25_s16 : Seg.bok PrimData25.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s16

theorem checked25_s17 : Seg.bok PrimData25.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s17

theorem checked25_s18 : Seg.bok PrimData25.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s18

theorem checked25_s19 : Seg.bok PrimData25.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s19

theorem checked25_s20 : Seg.bok PrimData25.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s20

theorem checked25_s21 : Seg.bok PrimData25.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s21

theorem checked25_s22 : Seg.bok PrimData25.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s22

theorem checked25_s23 : Seg.bok PrimData25.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s23

theorem checked25_s24 : Seg.bok PrimData25.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s24

theorem checked25_s25 : Seg.bok PrimData25.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s25

theorem checked25_s26 : Seg.bok PrimData25.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s26

theorem checked25_s27 : Seg.bok PrimData25.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s27

theorem checked25_s28 : Seg.bok PrimData25.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s28

theorem checked25_s29 : Seg.bok PrimData25.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s29

theorem checked25_s30 : Seg.bok PrimData25.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s30

theorem checked25_s31 : Seg.bok PrimData25.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s31

theorem checked25_s32 : Seg.bok PrimData25.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s32

theorem checked25_s33 : Seg.bok PrimData25.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s33

theorem checked25_s34 : Seg.bok PrimData25.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25_s34

 theorem checked25 : ∀ s ∈ PrimData25.segs, (Seg.bok s) = true := by
  unfold PrimData25.segs
  exact List.forall_mem_cons.2 ⟨checked25_s0, List.forall_mem_cons.2 ⟨checked25_s1, List.forall_mem_cons.2 ⟨checked25_s2, List.forall_mem_cons.2 ⟨checked25_s3, List.forall_mem_cons.2 ⟨checked25_s4, List.forall_mem_cons.2 ⟨checked25_s5, List.forall_mem_cons.2 ⟨checked25_s6, List.forall_mem_cons.2 ⟨checked25_s7, List.forall_mem_cons.2 ⟨checked25_s8, List.forall_mem_cons.2 ⟨checked25_s9, List.forall_mem_cons.2 ⟨checked25_s10, List.forall_mem_cons.2 ⟨checked25_s11, List.forall_mem_cons.2 ⟨checked25_s12, List.forall_mem_cons.2 ⟨checked25_s13, List.forall_mem_cons.2 ⟨checked25_s14, List.forall_mem_cons.2 ⟨checked25_s15, List.forall_mem_cons.2 ⟨checked25_s16, List.forall_mem_cons.2 ⟨checked25_s17, List.forall_mem_cons.2 ⟨checked25_s18, List.forall_mem_cons.2 ⟨checked25_s19, List.forall_mem_cons.2 ⟨checked25_s20, List.forall_mem_cons.2 ⟨checked25_s21, List.forall_mem_cons.2 ⟨checked25_s22, List.forall_mem_cons.2 ⟨checked25_s23, List.forall_mem_cons.2 ⟨checked25_s24, List.forall_mem_cons.2 ⟨checked25_s25, List.forall_mem_cons.2 ⟨checked25_s26, List.forall_mem_cons.2 ⟨checked25_s27, List.forall_mem_cons.2 ⟨checked25_s28, List.forall_mem_cons.2 ⟨checked25_s29, List.forall_mem_cons.2 ⟨checked25_s30, List.forall_mem_cons.2 ⟨checked25_s31, List.forall_mem_cons.2 ⟨checked25_s32, List.forall_mem_cons.2 ⟨checked25_s33, List.forall_mem_singleton.2 checked25_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked25
