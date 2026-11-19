/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_33.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/4b4636ad-6b72-4e54-9a0d-100905faa026
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData33.s0 : Seg := ⟨371815164270101001444265379, 371815164270101008495171606, 20160515, 4096, [], 371972157803601155732239282, 371972157803601162786122928⟩
def PrimData33.s1 : Seg := ⟨371972157803601155732239282, 371972157803601162786122928, 20168707, 4096, [], 372128534532390405304693535, 372128534532390412361542725⟩
def PrimData33.s2 : Seg := ⟨372128534532390405304693535, 372128534532390412361542725, 20176899, 4096, [], 372283984190277526200523581, 372283984190277533260320186⟩
def PrimData33.s3 : Seg := ⟨372283984190277526200523581, 372283984190277533260320186, 20185091, 4096, [], 372431059904182926198616892, 372431059904182933261202781⟩
def PrimData33.s4 : Seg := ⟨372431059904182926198616892, 372431059904182933261202781, 20193283, 4096, [], 372580001003556916920387238, 372580001003556923985797537⟩
def PrimData33.s5 : Seg := ⟨372580001003556916920387238, 372580001003556923985797537, 20201475, 4096, [], 372726152896243740425482547, 372726152896243747493663438⟩
def PrimData33.s6 : Seg := ⟨372726152896243740425482547, 372726152896243747493663438, 20209667, 4096, [], 372869205227635973981552671, 372869205227635981052445606⟩
def PrimData33.s7 : Seg := ⟨372869205227635973981552671, 372869205227635981052445606, 20217859, 4096, [], 373020639569701467037481161, 373020639569701474111245760⟩
def PrimData33.s8 : Seg := ⟨373020639569701467037481161, 373020639569701474111245760, 20226051, 4096, [], 373173008580371605471633173, 373173008580371612548286730⟩
def PrimData33.s9 : Seg := ⟨373173008580371605471633173, 373173008580371612548286730, 20234243, 4096, [], 373326001870074445470173790, 373326001870074452549728246⟩
def PrimData33.s10 : Seg := ⟨373326001870074445470173790, 373326001870074452549728246, 20242435, 4096, [], 373478378140989832062941443, 373478378140989839145385820⟩
def PrimData33.s11 : Seg := ⟨373478378140989832062941443, 373478378140989839145385820, 20250627, 4096, [], 373625171856335376162602416, 373625171856335383247829417⟩
def PrimData33.s12 : Seg := ⟨373625171856335376162602416, 373625171856335383247829417, 20258819, 4096, [], 373780969335631970423969952, 373780969335631977512151059⟩
def PrimData33.s13 : Seg := ⟨373780969335631970423969952, 373780969335631977512151059, 20267011, 4096, [], 373926218376252593599090613, 373926218376252600690025889⟩
def PrimData33.s14 : Seg := ⟨373926218376252593599090613, 373926218376252600690025889, 20275203, 4096, [], 374081713022696340236433186, 374081713022696347330317049⟩
def PrimData33.s15 : Seg := ⟨374081713022696340236433186, 374081713022696347330317049, 20283395, 4096, [], 374228520838026091906288175, 374228520838026099002955653⟩
def PrimData33.s16 : Seg := ⟨374228520838026091906288175, 374228520838026099002955653, 20291587, 4096, [], 374377194501895002789665282, 374377194501895009889151203⟩
def PrimData33.s17 : Seg := ⟨374377194501895002789665282, 374377194501895009889151203, 20299779, 4096, [], 374529906833653131290357263, 374529906833653138392738935⟩
def PrimData33.s18 : Seg := ⟨374529906833653131290357263, 374529906833653138392738935, 20307971, 4096, [], 374683864394720141511164833, 374683864394720148616466702⟩
def PrimData33.s19 : Seg := ⟨374683864394720141511164833, 374683864394720148616466702, 20316163, 4096, [], 374836273593403167964817618, 374836273593403175073009637⟩
def PrimData33.s20 : Seg := ⟨374836273593403167964817618, 374836273593403175073009637, 20324355, 4096, [], 374979684530364844481337877, 374979684530364851592248956⟩
def PrimData33.s21 : Seg := ⟨374979684530364844481337877, 374979684530364851592248956, 20332547, 4096, [], 375127444737988764962299583, 375127444737988772076012373⟩
def PrimData33.s22 : Seg := ⟨375127444737988764962299583, 375127444737988772076012373, 20340739, 4096, [], 375281106616925882136217289, 375281106616925889252843666⟩
def PrimData33.s23 : Seg := ⟨375281106616925882136217289, 375281106616925889252843666, 20348931, 4096, [], 375432288693484891103012202, 375432288693484898222504138⟩
def PrimData33.s24 : Seg := ⟨375432288693484891103012202, 375432288693484898222504138, 20357123, 4096, [], 375590614579500835559989092, 375590614579500842682483905⟩
def PrimData33.s25 : Seg := ⟨375590614579500835559989092, 375590614579500842682483905, 20365315, 4096, [], 375736526168340408838868246, 375736526168340415964129703⟩
def PrimData33.s26 : Seg := ⟨375736526168340408838868246, 375736526168340415964129703, 20373507, 4096, [], 375892686369582736504655764, 375892686369582743632878340⟩
def PrimData33.s27 : Seg := ⟨375892686369582736504655764, 375892686369582743632878340, 20381699, 4096, [], 376046366601662217239702622, 376046366601662224370839850⟩
def PrimData33.s28 : Seg := ⟨376046366601662217239702622, 376046366601662224370839850, 20389891, 4096, [], 376192599195247166368887991, 376192599195247173502797706⟩
def PrimData33.s29 : Seg := ⟨376192599195247166368887991, 376192599195247173502797706, 20398083, 4096, [], 376343181975476840143995136, 376343181975476847280760358⟩
def PrimData33.s30 : Seg := ⟨376343181975476840143995136, 376343181975476847280760358, 20406275, 4096, [], 376483832757132736590042432, 376483832757132743729474569⟩
def PrimData33.s31 : Seg := ⟨376483832757132736590042432, 376483832757132743729474569, 20414467, 4096, [], 376635354171185063718632207, 376635354171185070860937543⟩
def PrimData33.s32 : Seg := ⟨376635354171185063718632207, 376635354171185070860937543, 20422659, 4096, [], 376788431715369131900367864, 376788431715369139045576025⟩
def PrimData33.s33 : Seg := ⟨376788431715369131900367864, 376788431715369139045576025, 20430851, 4096, [], 376933129128787651749375852, 376933129128787658897326728⟩
def PrimData33.s34 : Seg := ⟨376933129128787651749375852, 376933129128787658897326728, 20439043, 4096, [], 377081245734728501937619077, 377081245734728509088378880⟩

def PrimData33.segs : List Seg := [PrimData33.s0, PrimData33.s1, PrimData33.s2, PrimData33.s3, PrimData33.s4, PrimData33.s5, PrimData33.s6, PrimData33.s7, PrimData33.s8, PrimData33.s9, PrimData33.s10, PrimData33.s11, PrimData33.s12, PrimData33.s13, PrimData33.s14, PrimData33.s15, PrimData33.s16, PrimData33.s17, PrimData33.s18, PrimData33.s19, PrimData33.s20, PrimData33.s21, PrimData33.s22, PrimData33.s23, PrimData33.s24, PrimData33.s25, PrimData33.s26, PrimData33.s27, PrimData33.s28, PrimData33.s29, PrimData33.s30, PrimData33.s31, PrimData33.s32, PrimData33.s33, PrimData33.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked33_s0 : Seg.bok PrimData33.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s0

theorem checked33_s1 : Seg.bok PrimData33.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s1

theorem checked33_s2 : Seg.bok PrimData33.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s2

theorem checked33_s3 : Seg.bok PrimData33.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s3

theorem checked33_s4 : Seg.bok PrimData33.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s4

theorem checked33_s5 : Seg.bok PrimData33.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s5

theorem checked33_s6 : Seg.bok PrimData33.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s6

theorem checked33_s7 : Seg.bok PrimData33.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s7

theorem checked33_s8 : Seg.bok PrimData33.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s8

theorem checked33_s9 : Seg.bok PrimData33.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s9

theorem checked33_s10 : Seg.bok PrimData33.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s10

theorem checked33_s11 : Seg.bok PrimData33.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s11

theorem checked33_s12 : Seg.bok PrimData33.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s12

theorem checked33_s13 : Seg.bok PrimData33.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s13

theorem checked33_s14 : Seg.bok PrimData33.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s14

theorem checked33_s15 : Seg.bok PrimData33.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s15

theorem checked33_s16 : Seg.bok PrimData33.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s16

theorem checked33_s17 : Seg.bok PrimData33.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s17

theorem checked33_s18 : Seg.bok PrimData33.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s18

theorem checked33_s19 : Seg.bok PrimData33.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s19

theorem checked33_s20 : Seg.bok PrimData33.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s20

theorem checked33_s21 : Seg.bok PrimData33.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s21

theorem checked33_s22 : Seg.bok PrimData33.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s22

theorem checked33_s23 : Seg.bok PrimData33.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s23

theorem checked33_s24 : Seg.bok PrimData33.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s24

theorem checked33_s25 : Seg.bok PrimData33.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s25

theorem checked33_s26 : Seg.bok PrimData33.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s26

theorem checked33_s27 : Seg.bok PrimData33.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s27

theorem checked33_s28 : Seg.bok PrimData33.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s28

theorem checked33_s29 : Seg.bok PrimData33.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s29

theorem checked33_s30 : Seg.bok PrimData33.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s30

theorem checked33_s31 : Seg.bok PrimData33.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s31

theorem checked33_s32 : Seg.bok PrimData33.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s32

theorem checked33_s33 : Seg.bok PrimData33.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s33

theorem checked33_s34 : Seg.bok PrimData33.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33_s34

 theorem checked33 : ∀ s ∈ PrimData33.segs, (Seg.bok s) = true := by
  unfold PrimData33.segs
  exact List.forall_mem_cons.2 ⟨checked33_s0, List.forall_mem_cons.2 ⟨checked33_s1, List.forall_mem_cons.2 ⟨checked33_s2, List.forall_mem_cons.2 ⟨checked33_s3, List.forall_mem_cons.2 ⟨checked33_s4, List.forall_mem_cons.2 ⟨checked33_s5, List.forall_mem_cons.2 ⟨checked33_s6, List.forall_mem_cons.2 ⟨checked33_s7, List.forall_mem_cons.2 ⟨checked33_s8, List.forall_mem_cons.2 ⟨checked33_s9, List.forall_mem_cons.2 ⟨checked33_s10, List.forall_mem_cons.2 ⟨checked33_s11, List.forall_mem_cons.2 ⟨checked33_s12, List.forall_mem_cons.2 ⟨checked33_s13, List.forall_mem_cons.2 ⟨checked33_s14, List.forall_mem_cons.2 ⟨checked33_s15, List.forall_mem_cons.2 ⟨checked33_s16, List.forall_mem_cons.2 ⟨checked33_s17, List.forall_mem_cons.2 ⟨checked33_s18, List.forall_mem_cons.2 ⟨checked33_s19, List.forall_mem_cons.2 ⟨checked33_s20, List.forall_mem_cons.2 ⟨checked33_s21, List.forall_mem_cons.2 ⟨checked33_s22, List.forall_mem_cons.2 ⟨checked33_s23, List.forall_mem_cons.2 ⟨checked33_s24, List.forall_mem_cons.2 ⟨checked33_s25, List.forall_mem_cons.2 ⟨checked33_s26, List.forall_mem_cons.2 ⟨checked33_s27, List.forall_mem_cons.2 ⟨checked33_s28, List.forall_mem_cons.2 ⟨checked33_s29, List.forall_mem_cons.2 ⟨checked33_s30, List.forall_mem_cons.2 ⟨checked33_s31, List.forall_mem_cons.2 ⟨checked33_s32, List.forall_mem_cons.2 ⟨checked33_s33, List.forall_mem_singleton.2 checked33_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked33
