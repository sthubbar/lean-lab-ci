/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_57.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/07add3b9-193a-404c-b4fd-fc77c01d1dfe
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData57.s0 : Seg := ⟨498724483918450097211217876, 498724483918450106668755047, 27041795, 4096, [], 498876957346179723151698599, 498876957346179732612127191⟩
def PrimData57.s1 : Seg := ⟨498876957346179723151698599, 498876957346179732612127191, 27049987, 4096, [], 499029749162923401513634772, 499029749162923410976960078⟩
def PrimData57.s2 : Seg := ⟨499029749162923401513634772, 499029749162923410976960078, 27058179, 4096, [], 499181912294473303443327528, 499181912294473312909537633⟩
def PrimData57.s3 : Seg := ⟨499181912294473303443327528, 499181912294473312909537633, 27066371, 4096, [], 499334709527726967803385158, 499334709527726977272492238⟩
def PrimData57.s4 : Seg := ⟨499334709527726967803385158, 499334709527726977272492238, 27074563, 4096, [], 499492244968331612072902976, 499492244968331621544996793⟩
def PrimData57.s5 : Seg := ⟨499492244968331612072902976, 499492244968331621544996793, 27082755, 4096, [], 499646941856079280816431749, 499646941856079290291458525⟩
def PrimData57.s6 : Seg := ⟨499646941856079280816431749, 499646941856079290291458525, 27090947, 4096, [], 499802904273023105840160563, 499802904273023115318143815⟩
def PrimData57.s7 : Seg := ⟨499802904273023105840160563, 499802904273023115318143815, 27099139, 4096, [], 499949082142334944986120433, 499949082142334954466874113⟩
def PrimData57.s8 : Seg := ⟨499949082142334944986120433, 499949082142334954466874113, 27107331, 4096, [], 500099367055421441859053798, 500099367055421451342656637⟩
def PrimData57.s9 : Seg := ⟨500099367055421441859053798, 500099367055421451342656637, 27115523, 4096, [], 500249338890168950454862197, 500249338890168959941308864⟩
def PrimData57.s10 : Seg := ⟨500249338890168950454862197, 500249338890168959941308864, 27123715, 4096, [], 500403733685632462014653701, 500403733685632471504028066⟩
def PrimData57.s11 : Seg := ⟨500403733685632462014653701, 500403733685632471504028066, 27131907, 4096, [], 500556868253789294370746500, 500556868253789303863023357⟩
def PrimData57.s12 : Seg := ⟨500556868253789294370746500, 500556868253789303863023357, 27140099, 4096, [], 500711268518173269220511570, 500711268518173278715715801⟩
def PrimData57.s13 : Seg := ⟨500711268518173269220511570, 500711268518173278715715801, 27148291, 4096, [], 500861566677377642244963565, 500861566677377651743017429⟩
def PrimData57.s14 : Seg := ⟨500861566677377642244963565, 500861566677377651743017429, 27156483, 4096, [], 501012498949471893403876259, 501012498949471902904791639⟩
def PrimData57.s15 : Seg := ⟨501012498949471893403876259, 501012498949471902904791639, 27164675, 4096, [], 501159644761947532376202347, 501159644761947541879906914⟩
def PrimData57.s16 : Seg := ⟨501159644761947532376202347, 501159644761947541879906914, 27172867, 4096, [], 501316582002963602661960902, 501316582002963612168641747⟩
def PrimData57.s17 : Seg := ⟨501316582002963602661960902, 501316582002963612168641747, 27181059, 4096, [], 501461522566217971583675696, 501461522566217981093103024⟩
def PrimData57.s18 : Seg := ⟨501461522566217971583675696, 501461522566217981093103024, 27189251, 4096, [], 501606465672307010012965285, 501606465672307019525139805⟩
def PrimData57.s19 : Seg := ⟨501606465672307010012965285, 501606465672307019525139805, 27197443, 4096, [], 501761516501334643259304963, 501761516501334652774418643⟩
def PrimData57.s20 : Seg := ⟨501761516501334643259304963, 501761516501334652774418643, 27205635, 4096, [], 501906780548774952084715105, 501906780548774961602582811⟩
def PrimData57.s21 : Seg := ⟨501906780548774952084715105, 501906780548774961602582811, 27213827, 4096, [], 502062468427558615090102553, 502062468427558624610922535⟩
def PrimData57.s22 : Seg := ⟨502062468427558615090102553, 502062468427558624610922535, 27222019, 4096, [], 502214369448270532013916157, 502214369448270541537615403⟩
def PrimData57.s23 : Seg := ⟨502214369448270532013916157, 502214369448270541537615403, 27230211, 4096, [], 502363746642822456597641904, 502363746642822466124173656⟩
def PrimData57.s24 : Seg := ⟨502363746642822456597641904, 502363746642822466124173656, 27238403, 4096, [], 502509336705232871659162755, 502509336705232881188455181⟩
def PrimData57.s25 : Seg := ⟨502509336705232871659162755, 502509336705232881188455181, 27246595, 4096, [], 502664088089872014910723939, 502664088089872024442950030⟩
def PrimData57.s26 : Seg := ⟨502664088089872014910723939, 502664088089872024442950030, 27254787, 4096, [], 502809051617244181877121821, 502809051617244191412096014⟩
def PrimData57.s27 : Seg := ⟨502809051617244181877121821, 502809051617244191412096014, 27262979, 4096, [], 502956228431844950836912685, 502956228431844960374677021⟩
def PrimData57.s28 : Seg := ⟨502956228431844950836912685, 502956228431844960374677021, 27271171, 4096, [], 503103092060682190752689835, 503103092060682200293238710⟩
def PrimData57.s29 : Seg := ⟨503103092060682190752689835, 503103092060682200293238710, 27279363, 4096, [], 503258486001726867261027157, 503258486001726876804522472⟩
def PrimData57.s30 : Seg := ⟨503258486001726867261027157, 503258486001726876804522472, 27287555, 4096, [], 503411987558720317958907272, 503411987558720327505313490⟩
def PrimData57.s31 : Seg := ⟨503411987558720317958907272, 503411987558720327505313490, 27295747, 4096, [], 503560438202272373343790090, 503560438202272382893010787⟩
def PrimData57.s32 : Seg := ⟨503560438202272373343790090, 503560438202272382893010787, 27303939, 4096, [], 503707312102180652286261868, 503707312102180661838267836⟩
def PrimData57.s33 : Seg := ⟨503707312102180652286261868, 503707312102180661838267836, 27312131, 4096, [], 503856715503588047712091023, 503856715503588057266929494⟩
def PrimData57.s34 : Seg := ⟨503856715503588047712091023, 503856715503588057266929494, 27320323, 4096, [], 504008332625792027011476429, 504008332625792036569189912⟩

def PrimData57.segs : List Seg := [PrimData57.s0, PrimData57.s1, PrimData57.s2, PrimData57.s3, PrimData57.s4, PrimData57.s5, PrimData57.s6, PrimData57.s7, PrimData57.s8, PrimData57.s9, PrimData57.s10, PrimData57.s11, PrimData57.s12, PrimData57.s13, PrimData57.s14, PrimData57.s15, PrimData57.s16, PrimData57.s17, PrimData57.s18, PrimData57.s19, PrimData57.s20, PrimData57.s21, PrimData57.s22, PrimData57.s23, PrimData57.s24, PrimData57.s25, PrimData57.s26, PrimData57.s27, PrimData57.s28, PrimData57.s29, PrimData57.s30, PrimData57.s31, PrimData57.s32, PrimData57.s33, PrimData57.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked57_s0 : Seg.bok PrimData57.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s0

theorem checked57_s1 : Seg.bok PrimData57.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s1

theorem checked57_s2 : Seg.bok PrimData57.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s2

theorem checked57_s3 : Seg.bok PrimData57.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s3

theorem checked57_s4 : Seg.bok PrimData57.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s4

theorem checked57_s5 : Seg.bok PrimData57.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s5

theorem checked57_s6 : Seg.bok PrimData57.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s6

theorem checked57_s7 : Seg.bok PrimData57.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s7

theorem checked57_s8 : Seg.bok PrimData57.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s8

theorem checked57_s9 : Seg.bok PrimData57.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s9

theorem checked57_s10 : Seg.bok PrimData57.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s10

theorem checked57_s11 : Seg.bok PrimData57.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s11

theorem checked57_s12 : Seg.bok PrimData57.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s12

theorem checked57_s13 : Seg.bok PrimData57.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s13

theorem checked57_s14 : Seg.bok PrimData57.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s14

theorem checked57_s15 : Seg.bok PrimData57.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s15

theorem checked57_s16 : Seg.bok PrimData57.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s16

theorem checked57_s17 : Seg.bok PrimData57.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s17

theorem checked57_s18 : Seg.bok PrimData57.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s18

theorem checked57_s19 : Seg.bok PrimData57.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s19

theorem checked57_s20 : Seg.bok PrimData57.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s20

theorem checked57_s21 : Seg.bok PrimData57.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s21

theorem checked57_s22 : Seg.bok PrimData57.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s22

theorem checked57_s23 : Seg.bok PrimData57.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s23

theorem checked57_s24 : Seg.bok PrimData57.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s24

theorem checked57_s25 : Seg.bok PrimData57.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s25

theorem checked57_s26 : Seg.bok PrimData57.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s26

theorem checked57_s27 : Seg.bok PrimData57.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s27

theorem checked57_s28 : Seg.bok PrimData57.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s28

theorem checked57_s29 : Seg.bok PrimData57.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s29

theorem checked57_s30 : Seg.bok PrimData57.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s30

theorem checked57_s31 : Seg.bok PrimData57.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s31

theorem checked57_s32 : Seg.bok PrimData57.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s32

theorem checked57_s33 : Seg.bok PrimData57.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s33

theorem checked57_s34 : Seg.bok PrimData57.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57_s34

 theorem checked57 : ∀ s ∈ PrimData57.segs, (Seg.bok s) = true := by
  unfold PrimData57.segs
  exact List.forall_mem_cons.2 ⟨checked57_s0, List.forall_mem_cons.2 ⟨checked57_s1, List.forall_mem_cons.2 ⟨checked57_s2, List.forall_mem_cons.2 ⟨checked57_s3, List.forall_mem_cons.2 ⟨checked57_s4, List.forall_mem_cons.2 ⟨checked57_s5, List.forall_mem_cons.2 ⟨checked57_s6, List.forall_mem_cons.2 ⟨checked57_s7, List.forall_mem_cons.2 ⟨checked57_s8, List.forall_mem_cons.2 ⟨checked57_s9, List.forall_mem_cons.2 ⟨checked57_s10, List.forall_mem_cons.2 ⟨checked57_s11, List.forall_mem_cons.2 ⟨checked57_s12, List.forall_mem_cons.2 ⟨checked57_s13, List.forall_mem_cons.2 ⟨checked57_s14, List.forall_mem_cons.2 ⟨checked57_s15, List.forall_mem_cons.2 ⟨checked57_s16, List.forall_mem_cons.2 ⟨checked57_s17, List.forall_mem_cons.2 ⟨checked57_s18, List.forall_mem_cons.2 ⟨checked57_s19, List.forall_mem_cons.2 ⟨checked57_s20, List.forall_mem_cons.2 ⟨checked57_s21, List.forall_mem_cons.2 ⟨checked57_s22, List.forall_mem_cons.2 ⟨checked57_s23, List.forall_mem_cons.2 ⟨checked57_s24, List.forall_mem_cons.2 ⟨checked57_s25, List.forall_mem_cons.2 ⟨checked57_s26, List.forall_mem_cons.2 ⟨checked57_s27, List.forall_mem_cons.2 ⟨checked57_s28, List.forall_mem_cons.2 ⟨checked57_s29, List.forall_mem_cons.2 ⟨checked57_s30, List.forall_mem_cons.2 ⟨checked57_s31, List.forall_mem_cons.2 ⟨checked57_s32, List.forall_mem_cons.2 ⟨checked57_s33, List.forall_mem_singleton.2 checked57_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked57
