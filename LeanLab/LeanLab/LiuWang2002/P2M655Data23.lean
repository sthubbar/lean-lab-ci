/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_23.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/0afc91f6-aeb8-4b56-9913-fb4129aa66f4
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData23.s0 : Seg := ⟨318914454335844904954429457, 318914454335844911002220552, 17293315, 4096, [], 319069093968574159514301515, 319069093968574165565027194⟩
def PrimData23.s1 : Seg := ⟨319069093968574159514301515, 319069093968574165565027194, 17301507, 4096, [], 319221278413521032162932848, 319221278413521038216546455⟩
def PrimData23.s2 : Seg := ⟨319221278413521032162932848, 319221278413521038216546455, 17309699, 4096, [], 319375926856429930520803886, 319375926856429936577352077⟩
def PrimData23.s3 : Seg := ⟨319375926856429930520803886, 319375926856429936577352077, 17317891, 4096, [], 319537651233675428925436811, 319537651233675434985053722⟩
def PrimData23.s4 : Seg := ⟨319537651233675428925436811, 319537651233675434985053722, 17326083, 4096, [], 319692923381697149972877747, 319692923381697156035440906⟩
def PrimData23.s5 : Seg := ⟨319692923381697149972877747, 319692923381697156035440906, 17334275, 4096, [], 319843587808141437388744873, 319843587808141443454166800⟩
def PrimData23.s6 : Seg := ⟨319843587808141437388744873, 319843587808141443454166800, 17342467, 4096, [], 319989029158486255422793106, 319989029158486261490974657⟩
def PrimData23.s7 : Seg := ⟨319989029158486255422793106, 319989029158486261490974657, 17350659, 4096, [], 320138779579218014300474738, 320138779579218020371497561⟩
def PrimData23.s8 : Seg := ⟨320138779579218014300474738, 320138779579218020371497561, 17358851, 4096, [], 320286381664073654852526829, 320286381664073660926350100⟩
def PrimData23.s9 : Seg := ⟨320286381664073654852526829, 320286381664073660926350100, 17367043, 4096, [], 320437678162458361737890145, 320437678162458367814583848⟩
def PrimData23.s10 : Seg := ⟨320437678162458361737890145, 320437678162458367814583848, 17375235, 4096, [], 320588671381005211144833722, 320588671381005217224392025⟩
def PrimData23.s11 : Seg := ⟨320588671381005211144833722, 320588671381005217224392025, 17383427, 4096, [], 320740898968389680498976031, 320740898968389686581422262⟩
def PrimData23.s12 : Seg := ⟨320740898968389680498976031, 320740898968389686581422262, 17391619, 4096, [], 320893745987608912640740516, 320893745987608918726086339⟩
def PrimData23.s13 : Seg := ⟨320893745987608912640740516, 320893745987608918726086339, 17399811, 4096, [], 321050902945199043880590908, 321050902945199049968917971⟩
def PrimData23.s14 : Seg := ⟨321050902945199043880590908, 321050902945199049968917971, 17408003, 4096, [], 321210217216139249795196446, 321210217216139255886545573⟩
def PrimData23.s15 : Seg := ⟨321210217216139249795196446, 321210217216139255886545573, 17416195, 4096, [], 321360616670100017048788712, 321360616670100023142990775⟩
def PrimData23.s16 : Seg := ⟨321360616670100017048788712, 321360616670100023142990775, 17424387, 4096, [], 321507021935241683488980935, 321507021935241689585960118⟩
def PrimData23.s17 : Seg := ⟨321507021935241683488980935, 321507021935241689585960118, 17432579, 4096, [], 321656814653967245918608589, 321656814653967252018429044⟩
def PrimData23.s18 : Seg := ⟨321656814653967245918608589, 321656814653967252018429044, 17440771, 4096, [], 321813378617639357325753878, 321813378617639363428543909⟩
def PrimData23.s19 : Seg := ⟨321813378617639357325753878, 321813378617639363428543909, 17448963, 4096, [], 321958258208353960163379301, 321958258208353966268917292⟩
def PrimData23.s20 : Seg := ⟨321958258208353960163379301, 321958258208353966268917292, 17457155, 4096, [], 322106525542499264699665112, 322106525542499270808015215⟩
def PrimData23.s21 : Seg := ⟨322106525542499264699665112, 322106525542499270808015215, 17465347, 4096, [], 322261257004493322702358974, 322261257004493328813643661⟩
def PrimData23.s22 : Seg := ⟨322261257004493322702358974, 322261257004493328813643661, 17473539, 4096, [], 322421837704104924933498734, 322421837704104931047828813⟩
def PrimData23.s23 : Seg := ⟨322421837704104924933498734, 322421837704104931047828813, 17481731, 4096, [], 322573193893593364253653823, 322573193893593370370854334⟩
def PrimData23.s24 : Seg := ⟨322573193893593364253653823, 322573193893593370370854334, 17489923, 4096, [], 322727323130001193320894365, 322727323130001199441017807⟩
def PrimData23.s25 : Seg := ⟨322727323130001193320894365, 322727323130001199441017807, 17498115, 4096, [], 322889147971257798224931264, 322889147971257804348123426⟩
def PrimData23.s26 : Seg := ⟨322889147971257798224931264, 322889147971257804348123426, 17506307, 4096, [], 323035902013851938521725193, 323035902013851944647700307⟩
def PrimData23.s27 : Seg := ⟨323035902013851938521725193, 323035902013851944647700307, 17514499, 4096, [], 323182044872073742006526077, 323182044872073748135272479⟩
def PrimData23.s28 : Seg := ⟨323182044872073742006526077, 323182044872073748135272479, 17522691, 4096, [], 323333114646072508544212080, 323333114646072514675823082⟩
def PrimData23.s29 : Seg := ⟨323333114646072508544212080, 323333114646072514675823082, 17530883, 4096, [], 323482650198094210357536153, 323482650198094216491982595⟩
def PrimData23.s30 : Seg := ⟨323482650198094210357536153, 323482650198094216491982595, 17539075, 4096, [], 323638343833319969264820780, 323638343833319975402219302⟩
def PrimData23.s31 : Seg := ⟨323638343833319969264820780, 323638343833319975402219302, 17547267, 4096, [], 323791580139303320770142121, 323791580139303326910446079⟩
def PrimData23.s32 : Seg := ⟨323791580139303320770142121, 323791580139303326910446079, 17555459, 4096, [], 323938974271201768677471079, 323938974271201774820569653⟩
def PrimData23.s33 : Seg := ⟨323938974271201768677471079, 323938974271201774820569653, 17563651, 4096, [], 324094680981442468796362101, 324094680981442474942412759⟩
def PrimData23.s34 : Seg := ⟨324094680981442468796362101, 324094680981442474942412759, 17571843, 4096, [], 324248237948278575996275807, 324248237948278582145237752⟩

def PrimData23.segs : List Seg := [PrimData23.s0, PrimData23.s1, PrimData23.s2, PrimData23.s3, PrimData23.s4, PrimData23.s5, PrimData23.s6, PrimData23.s7, PrimData23.s8, PrimData23.s9, PrimData23.s10, PrimData23.s11, PrimData23.s12, PrimData23.s13, PrimData23.s14, PrimData23.s15, PrimData23.s16, PrimData23.s17, PrimData23.s18, PrimData23.s19, PrimData23.s20, PrimData23.s21, PrimData23.s22, PrimData23.s23, PrimData23.s24, PrimData23.s25, PrimData23.s26, PrimData23.s27, PrimData23.s28, PrimData23.s29, PrimData23.s30, PrimData23.s31, PrimData23.s32, PrimData23.s33, PrimData23.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked23_s0 : Seg.bok PrimData23.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s0

theorem checked23_s1 : Seg.bok PrimData23.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s1

theorem checked23_s2 : Seg.bok PrimData23.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s2

theorem checked23_s3 : Seg.bok PrimData23.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s3

theorem checked23_s4 : Seg.bok PrimData23.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s4

theorem checked23_s5 : Seg.bok PrimData23.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s5

theorem checked23_s6 : Seg.bok PrimData23.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s6

theorem checked23_s7 : Seg.bok PrimData23.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s7

theorem checked23_s8 : Seg.bok PrimData23.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s8

theorem checked23_s9 : Seg.bok PrimData23.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s9

theorem checked23_s10 : Seg.bok PrimData23.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s10

theorem checked23_s11 : Seg.bok PrimData23.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s11

theorem checked23_s12 : Seg.bok PrimData23.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s12

theorem checked23_s13 : Seg.bok PrimData23.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s13

theorem checked23_s14 : Seg.bok PrimData23.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s14

theorem checked23_s15 : Seg.bok PrimData23.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s15

theorem checked23_s16 : Seg.bok PrimData23.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s16

theorem checked23_s17 : Seg.bok PrimData23.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s17

theorem checked23_s18 : Seg.bok PrimData23.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s18

theorem checked23_s19 : Seg.bok PrimData23.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s19

theorem checked23_s20 : Seg.bok PrimData23.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s20

theorem checked23_s21 : Seg.bok PrimData23.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s21

theorem checked23_s22 : Seg.bok PrimData23.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s22

theorem checked23_s23 : Seg.bok PrimData23.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s23

theorem checked23_s24 : Seg.bok PrimData23.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s24

theorem checked23_s25 : Seg.bok PrimData23.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s25

theorem checked23_s26 : Seg.bok PrimData23.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s26

theorem checked23_s27 : Seg.bok PrimData23.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s27

theorem checked23_s28 : Seg.bok PrimData23.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s28

theorem checked23_s29 : Seg.bok PrimData23.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s29

theorem checked23_s30 : Seg.bok PrimData23.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s30

theorem checked23_s31 : Seg.bok PrimData23.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s31

theorem checked23_s32 : Seg.bok PrimData23.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s32

theorem checked23_s33 : Seg.bok PrimData23.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s33

theorem checked23_s34 : Seg.bok PrimData23.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23_s34

 theorem checked23 : ∀ s ∈ PrimData23.segs, (Seg.bok s) = true := by
  unfold PrimData23.segs
  exact List.forall_mem_cons.2 ⟨checked23_s0, List.forall_mem_cons.2 ⟨checked23_s1, List.forall_mem_cons.2 ⟨checked23_s2, List.forall_mem_cons.2 ⟨checked23_s3, List.forall_mem_cons.2 ⟨checked23_s4, List.forall_mem_cons.2 ⟨checked23_s5, List.forall_mem_cons.2 ⟨checked23_s6, List.forall_mem_cons.2 ⟨checked23_s7, List.forall_mem_cons.2 ⟨checked23_s8, List.forall_mem_cons.2 ⟨checked23_s9, List.forall_mem_cons.2 ⟨checked23_s10, List.forall_mem_cons.2 ⟨checked23_s11, List.forall_mem_cons.2 ⟨checked23_s12, List.forall_mem_cons.2 ⟨checked23_s13, List.forall_mem_cons.2 ⟨checked23_s14, List.forall_mem_cons.2 ⟨checked23_s15, List.forall_mem_cons.2 ⟨checked23_s16, List.forall_mem_cons.2 ⟨checked23_s17, List.forall_mem_cons.2 ⟨checked23_s18, List.forall_mem_cons.2 ⟨checked23_s19, List.forall_mem_cons.2 ⟨checked23_s20, List.forall_mem_cons.2 ⟨checked23_s21, List.forall_mem_cons.2 ⟨checked23_s22, List.forall_mem_cons.2 ⟨checked23_s23, List.forall_mem_cons.2 ⟨checked23_s24, List.forall_mem_cons.2 ⟨checked23_s25, List.forall_mem_cons.2 ⟨checked23_s26, List.forall_mem_cons.2 ⟨checked23_s27, List.forall_mem_cons.2 ⟨checked23_s28, List.forall_mem_cons.2 ⟨checked23_s29, List.forall_mem_cons.2 ⟨checked23_s30, List.forall_mem_cons.2 ⟨checked23_s31, List.forall_mem_cons.2 ⟨checked23_s32, List.forall_mem_cons.2 ⟨checked23_s33, List.forall_mem_singleton.2 checked23_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked23
