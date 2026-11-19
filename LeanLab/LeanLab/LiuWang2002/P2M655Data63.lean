/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_63.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/26e63077-143a-4c0d-a67e-a025c50bfcdd
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData63.s0 : Seg := ⟨530468852286647568430227360, 530468852286647578489719982, 28762115, 4096, [], 530618073364281842921532018, 530618073364281852983853811⟩
def PrimData63.s1 : Seg := ⟨530618073364281842921532018, 530618073364281852983853811, 28770307, 4096, [], 530766663253553790800301591, 530766663253553800865440647⟩
def PrimData63.s2 : Seg := ⟨530766663253553790800301591, 530766663253553800865440647, 28778499, 4096, [], 530914938754467313400625887, 530914938754467323468577322⟩
def PrimData63.s3 : Seg := ⟨530914938754467313400625887, 530914938754467323468577322, 28786691, 4096, [], 531071771215150908186917871, 531071771215150918257844034⟩
def PrimData63.s4 : Seg := ⟨531071771215150908186917871, 531071771215150918257844034, 28794883, 4096, [], 531223853675534702508566540, 531223853675534712582377994⟩
def PrimData63.s5 : Seg := ⟨531223853675534702508566540, 531223853675534712582377994, 28803075, 4096, [], 531367067082848002729043061, 531367067082848012805570698⟩
def PrimData63.s6 : Seg := ⟨531367067082848002729043061, 531367067082848012805570698, 28811267, 4096, [], 531509966005281329467547996, 531509966005281339546785793⟩
def PrimData63.s7 : Seg := ⟨531509966005281329467547996, 531509966005281339546785793, 28819459, 4096, [], 531666808876574010221841981, 531666808876574020304054291⟩
def PrimData63.s8 : Seg := ⟨531666808876574010221841981, 531666808876574020304054291, 28827651, 4096, [], 531815732812832434978647534, 531815732812832445063684194⟩
def PrimData63.s9 : Seg := ⟨531815732812832434978647534, 531815732812832445063684194, 28835843, 4096, [], 531965292960397371031614849, 531965292960397381119487986⟩
def PrimData63.s10 : Seg := ⟨531965292960397371031614849, 531965292960397381119487986, 28844035, 4096, [], 532119291753934841300285501, 532119291753934851391079430⟩
def PrimData63.s11 : Seg := ⟨532119291753934841300285501, 532119291753934851391079430, 28852227, 4096, [], 532274560598734038789083319, 532274560598734048882821859⟩
def PrimData63.s12 : Seg := ⟨532274560598734038789083319, 532274560598734048882821859, 28860419, 4096, [], 532424445005592609249214483, 532424445005592619345795609⟩
def PrimData63.s13 : Seg := ⟨532424445005592609249214483, 532424445005592619345795609, 28868611, 4096, [], 532580669644494997458025701, 532580669644495007557568753⟩
def PrimData63.s14 : Seg := ⟨532580669644494997458025701, 532580669644495007557568753, 28876803, 4096, [], 532728340837815714774526344, 532728340837815724876869466⟩
def PrimData63.s15 : Seg := ⟨532728340837815714774526344, 532728340837815724876869466, 28884995, 4096, [], 532876648231463872356764350, 532876648231463882461919254⟩
def PrimData63.s16 : Seg := ⟨532876648231463872356764350, 532876648231463882461919254, 28893187, 4096, [], 533030979204080317534989051, 533030979204080327643071051⟩
def PrimData63.s17 : Seg := ⟨533030979204080317534989051, 533030979204080327643071051, 28901379, 4096, [], 533180242196787948337693222, 533180242196787958448605515⟩
def PrimData63.s18 : Seg := ⟨533180242196787948337693222, 533180242196787958448605515, 28909571, 4096, [], 533334895196622716250551372, 533334895196622726364395752⟩
def PrimData63.s19 : Seg := ⟨533334895196622716250551372, 533334895196622726364395752, 28917763, 4096, [], 533490818350548305362353820, 533490818350548315479155058⟩
def PrimData63.s20 : Seg := ⟨533490818350548305362353820, 533490818350548315479155058, 28925955, 4096, [], 533639771819589995035951766, 533639771819590005155577203⟩
def PrimData63.s21 : Seg := ⟨533639771819589995035951766, 533639771819590005155577203, 28934147, 4096, [], 533783339929056244068957848, 533783339929056254191305896⟩
def PrimData63.s22 : Seg := ⟨533783339929056244068957848, 533783339929056254191305896, 28942339, 4096, [], 533937686216155451679976830, 533937686216155461805251836⟩
def PrimData63.s23 : Seg := ⟨533937686216155451679976830, 533937686216155461805251836, 28950531, 4096, [], 534089182551419114344444129, 534089182551419124472590880⟩
def PrimData63.s24 : Seg := ⟨534089182551419114344444129, 534089182551419124472590880, 28958723, 4096, [], 534229588359718967514256442, 534229588359718977645064900⟩
def PrimData63.s25 : Seg := ⟨534229588359718967514256442, 534229588359718977645064900, 28966915, 4096, [], 534381406592882793813528410, 534381406592882803947216269⟩
def PrimData63.s26 : Seg := ⟨534381406592882793813528410, 534381406592882803947216269, 28975107, 4096, [], 534535129065766427815493843, 534535129065766437952096840⟩
def PrimData63.s27 : Seg := ⟨534535129065766427815493843, 534535129065766437952096840, 28983299, 4096, [], 534691706724314043590830318, 534691706724314053730402342⟩
def PrimData63.s28 : Seg := ⟨534691706724314043590830318, 534691706724314053730402342, 28991491, 4096, [], 534840679835932969254804018, 534840679835932979397200579⟩
def PrimData63.s29 : Seg := ⟨534840679835932969254804018, 534840679835932979397200579, 28999683, 4096, [], 534991240216434349516965109, 534991240216434359662215482⟩
def PrimData63.s30 : Seg := ⟨534991240216434349516965109, 534991240216434359662215482, 29007875, 4096, [], 535145289824759984119560352, 535145289824759994267732064⟩
def PrimData63.s31 : Seg := ⟨535145289824759984119560352, 535145289824759994267732064, 29016067, 4096, [], 535293319337373033568250280, 535293319337373043719228124⟩
def PrimData63.s32 : Seg := ⟨535293319337373033568250280, 535293319337373043719228124, 29024259, 4096, [], 535448324932386113053142676, 535448324932386123207060229⟩
def PrimData63.s33 : Seg := ⟨535448324932386113053142676, 535448324932386123207060229, 29032451, 4096, [], 535599529215603984586909104, 535599529215603994743693335⟩
def PrimData63.s34 : Seg := ⟨535599529215603984586909104, 535599529215603994743693335, 29040643, 4096, [], 535750101994031776849775186, 535750101994031787009414183⟩

def PrimData63.segs : List Seg := [PrimData63.s0, PrimData63.s1, PrimData63.s2, PrimData63.s3, PrimData63.s4, PrimData63.s5, PrimData63.s6, PrimData63.s7, PrimData63.s8, PrimData63.s9, PrimData63.s10, PrimData63.s11, PrimData63.s12, PrimData63.s13, PrimData63.s14, PrimData63.s15, PrimData63.s16, PrimData63.s17, PrimData63.s18, PrimData63.s19, PrimData63.s20, PrimData63.s21, PrimData63.s22, PrimData63.s23, PrimData63.s24, PrimData63.s25, PrimData63.s26, PrimData63.s27, PrimData63.s28, PrimData63.s29, PrimData63.s30, PrimData63.s31, PrimData63.s32, PrimData63.s33, PrimData63.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked63_s0 : Seg.bok PrimData63.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s0

theorem checked63_s1 : Seg.bok PrimData63.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s1

theorem checked63_s2 : Seg.bok PrimData63.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s2

theorem checked63_s3 : Seg.bok PrimData63.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s3

theorem checked63_s4 : Seg.bok PrimData63.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s4

theorem checked63_s5 : Seg.bok PrimData63.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s5

theorem checked63_s6 : Seg.bok PrimData63.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s6

theorem checked63_s7 : Seg.bok PrimData63.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s7

theorem checked63_s8 : Seg.bok PrimData63.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s8

theorem checked63_s9 : Seg.bok PrimData63.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s9

theorem checked63_s10 : Seg.bok PrimData63.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s10

theorem checked63_s11 : Seg.bok PrimData63.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s11

theorem checked63_s12 : Seg.bok PrimData63.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s12

theorem checked63_s13 : Seg.bok PrimData63.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s13

theorem checked63_s14 : Seg.bok PrimData63.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s14

theorem checked63_s15 : Seg.bok PrimData63.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s15

theorem checked63_s16 : Seg.bok PrimData63.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s16

theorem checked63_s17 : Seg.bok PrimData63.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s17

theorem checked63_s18 : Seg.bok PrimData63.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s18

theorem checked63_s19 : Seg.bok PrimData63.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s19

theorem checked63_s20 : Seg.bok PrimData63.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s20

theorem checked63_s21 : Seg.bok PrimData63.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s21

theorem checked63_s22 : Seg.bok PrimData63.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s22

theorem checked63_s23 : Seg.bok PrimData63.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s23

theorem checked63_s24 : Seg.bok PrimData63.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s24

theorem checked63_s25 : Seg.bok PrimData63.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s25

theorem checked63_s26 : Seg.bok PrimData63.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s26

theorem checked63_s27 : Seg.bok PrimData63.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s27

theorem checked63_s28 : Seg.bok PrimData63.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s28

theorem checked63_s29 : Seg.bok PrimData63.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s29

theorem checked63_s30 : Seg.bok PrimData63.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s30

theorem checked63_s31 : Seg.bok PrimData63.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s31

theorem checked63_s32 : Seg.bok PrimData63.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s32

theorem checked63_s33 : Seg.bok PrimData63.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s33

theorem checked63_s34 : Seg.bok PrimData63.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63_s34

 theorem checked63 : ∀ s ∈ PrimData63.segs, (Seg.bok s) = true := by
  unfold PrimData63.segs
  exact List.forall_mem_cons.2 ⟨checked63_s0, List.forall_mem_cons.2 ⟨checked63_s1, List.forall_mem_cons.2 ⟨checked63_s2, List.forall_mem_cons.2 ⟨checked63_s3, List.forall_mem_cons.2 ⟨checked63_s4, List.forall_mem_cons.2 ⟨checked63_s5, List.forall_mem_cons.2 ⟨checked63_s6, List.forall_mem_cons.2 ⟨checked63_s7, List.forall_mem_cons.2 ⟨checked63_s8, List.forall_mem_cons.2 ⟨checked63_s9, List.forall_mem_cons.2 ⟨checked63_s10, List.forall_mem_cons.2 ⟨checked63_s11, List.forall_mem_cons.2 ⟨checked63_s12, List.forall_mem_cons.2 ⟨checked63_s13, List.forall_mem_cons.2 ⟨checked63_s14, List.forall_mem_cons.2 ⟨checked63_s15, List.forall_mem_cons.2 ⟨checked63_s16, List.forall_mem_cons.2 ⟨checked63_s17, List.forall_mem_cons.2 ⟨checked63_s18, List.forall_mem_cons.2 ⟨checked63_s19, List.forall_mem_cons.2 ⟨checked63_s20, List.forall_mem_cons.2 ⟨checked63_s21, List.forall_mem_cons.2 ⟨checked63_s22, List.forall_mem_cons.2 ⟨checked63_s23, List.forall_mem_cons.2 ⟨checked63_s24, List.forall_mem_cons.2 ⟨checked63_s25, List.forall_mem_cons.2 ⟨checked63_s26, List.forall_mem_cons.2 ⟨checked63_s27, List.forall_mem_cons.2 ⟨checked63_s28, List.forall_mem_cons.2 ⟨checked63_s29, List.forall_mem_cons.2 ⟨checked63_s30, List.forall_mem_cons.2 ⟨checked63_s31, List.forall_mem_cons.2 ⟨checked63_s32, List.forall_mem_cons.2 ⟨checked63_s33, List.forall_mem_singleton.2 checked63_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked63
