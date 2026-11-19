/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_24.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/bd6e25b3-55d1-4519-a791-bff80ee75641
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData24.s0 : Seg := ⟨324248237948278575996275807, 324248237948278582145237752, 17580035, 4096, [], 324399952761964308484297542, 324399952761964314636135751⟩
def PrimData24.s1 : Seg := ⟨324399952761964308484297542, 324399952761964314636135751, 17588227, 4096, [], 324549209796029364041601342, 324549209796029370196269159⟩
def PrimData24.s2 : Seg := ⟨324549209796029364041601342, 324549209796029370196269159, 17596419, 4096, [], 324694470201307932840698247, 324694470201307938998119865⟩
def PrimData24.s3 : Seg := ⟨324694470201307932840698247, 324694470201307938998119865, 17604611, 4096, [], 324844966644662500900334195, 324844966644662507060608750⟩
def PrimData24.s4 : Seg := ⟨324844966644662500900334195, 324844966644662507060608750, 17612803, 4096, [], 324994543964622250028711451, 324994543964622256191821460⟩
def PrimData24.s5 : Seg := ⟨324994543964622250028711451, 324994543964622256191821460, 17620995, 4096, [], 325149357659015668648828650, 325149357659015674814873264⟩
def PrimData24.s6 : Seg := ⟨325149357659015668648828650, 325149357659015674814873264, 17629187, 4096, [], 325303867911060095132867356, 325303867911060101301840993⟩
def PrimData24.s7 : Seg := ⟨325303867911060095132867356, 325303867911060101301840993, 17637379, 4096, [], 325457459067444305523960891, 325457459067444311695845858⟩
def PrimData24.s8 : Seg := ⟨325457459067444305523960891, 325457459067444311695845858, 17645571, 4096, [], 325601512558310872751400177, 325601512558310878926015611⟩
def PrimData24.s9 : Seg := ⟨325601512558310872751400177, 325601512558310878926015611, 17653763, 4096, [], 325749879464292785472307249, 325749879464292791649734808⟩
def PrimData24.s10 : Seg := ⟨325749879464292785472307249, 325749879464292791649734808, 17661955, 4096, [], 325896711387948013244315053, 325896711387948019424525675⟩
def PrimData24.s11 : Seg := ⟨325896711387948013244315053, 325896711387948019424525675, 17670147, 4096, [], 326044470875122292223706972, 326044470875122298406718042⟩
def PrimData24.s12 : Seg := ⟨326044470875122292223706972, 326044470875122298406718042, 17678339, 4096, [], 326199314805120731081687091, 326199314805120737267632920⟩
def PrimData24.s13 : Seg := ⟨326199314805120731081687091, 326199314805120737267632920, 17686531, 4096, [], 326352008094109500442218731, 326352008094109506631058581⟩
def PrimData24.s14 : Seg := ⟨326352008094109500442218731, 326352008094109506631058581, 17694723, 4096, [], 326502858403356506986961098, 326502858403356513178659938⟩
def PrimData24.s15 : Seg := ⟨326502858403356506986961098, 326502858403356513178659938, 17702915, 4096, [], 326654020766556958840040592, 326654020766556965034604279⟩
def PrimData24.s16 : Seg := ⟨326654020766556958840040592, 326654020766556965034604279, 17711107, 4096, [], 326800261368272141570658821, 326800261368272147767994153⟩
def PrimData24.s17 : Seg := ⟨326800261368272141570658821, 326800261368272147767994153, 17719299, 4096, [], 326950816346571855940333192, 326950816346571862140521836⟩
def PrimData24.s18 : Seg := ⟨326950816346571855940333192, 326950816346571862140521836, 17727491, 4096, [], 327105070185378110421799108, 327105070185378116624910997⟩
def PrimData24.s19 : Seg := ⟨327105070185378110421799108, 327105070185378116624910997, 17735683, 4096, [], 327254094026302911704255485, 327254094026302917910191326⟩
def PrimData24.s20 : Seg := ⟨327254094026302911704255485, 327254094026302917910191326, 17743875, 4096, [], 327395424260700538314194305, 327395424260700544522808479⟩
def PrimData24.s21 : Seg := ⟨327395424260700538314194305, 327395424260700544522808479, 17752067, 4096, [], 327547535534009813005920788, 327547535534009819217417721⟩
def PrimData24.s22 : Seg := ⟨327547535534009813005920788, 327547535534009819217417721, 17760259, 4096, [], 327694108345140821432553990, 327694108345140827646828446⟩
def PrimData24.s23 : Seg := ⟨327694108345140821432553990, 327694108345140827646828446, 17768451, 4096, [], 327852078829930208754319468, 327852078829930214971587593⟩
def PrimData24.s24 : Seg := ⟨327852078829930208754319468, 327852078829930214971587593, 17776643, 4096, [], 328002970956302153682207565, 328002970956302159902335499⟩
def PrimData24.s25 : Seg := ⟨328002970956302153682207565, 328002970956302159902335499, 17784835, 4096, [], 328163105754319636445385105, 328163105754319642668548544⟩
def PrimData24.s26 : Seg := ⟨328163105754319636445385105, 328163105754319642668548544, 17793027, 4096, [], 328309694625220349870396884, 328309694625220356096338749⟩
def PrimData24.s27 : Seg := ⟨328309694625220349870396884, 328309694625220356096338749, 17801219, 4096, [], 328466758586376871404878361, 328466758586376877633797211⟩
def PrimData24.s28 : Seg := ⟨328466758586376871404878361, 328466758586376877633797211, 17809411, 4096, [], 328614279586857938806789243, 328614279586857945038503556⟩
def PrimData24.s29 : Seg := ⟨328614279586857938806789243, 328614279586857945038503556, 17817603, 4096, [], 328763036607798005802627723, 328763036607798012037160798⟩
def PrimData24.s30 : Seg := ⟨328763036607798005802627723, 328763036607798012037160798, 17825795, 4096, [], 328911181747746334146485264, 328911181747746340383825343⟩
def PrimData24.s31 : Seg := ⟨328911181747746334146485264, 328911181747746340383825343, 17833987, 4096, [], 329058098896461047579037759, 329058098896461053819161538⟩
def PrimData24.s32 : Seg := ⟨329058098896461047579037759, 329058098896461053819161538, 17842179, 4096, [], 329206560136834400363480536, 329206560136834406606417807⟩
def PrimData24.s33 : Seg := ⟨329206560136834400363480536, 329206560136834406606417807, 17850371, 4096, [], 329354101399642052620167090, 329354101399642058865900097⟩
def PrimData24.s34 : Seg := ⟨329354101399642052620167090, 329354101399642058865900097, 17858563, 4096, [], 329517356150278026131463925, 329517356150278032380290523⟩

def PrimData24.segs : List Seg := [PrimData24.s0, PrimData24.s1, PrimData24.s2, PrimData24.s3, PrimData24.s4, PrimData24.s5, PrimData24.s6, PrimData24.s7, PrimData24.s8, PrimData24.s9, PrimData24.s10, PrimData24.s11, PrimData24.s12, PrimData24.s13, PrimData24.s14, PrimData24.s15, PrimData24.s16, PrimData24.s17, PrimData24.s18, PrimData24.s19, PrimData24.s20, PrimData24.s21, PrimData24.s22, PrimData24.s23, PrimData24.s24, PrimData24.s25, PrimData24.s26, PrimData24.s27, PrimData24.s28, PrimData24.s29, PrimData24.s30, PrimData24.s31, PrimData24.s32, PrimData24.s33, PrimData24.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked24_s0 : Seg.bok PrimData24.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s0

theorem checked24_s1 : Seg.bok PrimData24.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s1

theorem checked24_s2 : Seg.bok PrimData24.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s2

theorem checked24_s3 : Seg.bok PrimData24.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s3

theorem checked24_s4 : Seg.bok PrimData24.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s4

theorem checked24_s5 : Seg.bok PrimData24.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s5

theorem checked24_s6 : Seg.bok PrimData24.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s6

theorem checked24_s7 : Seg.bok PrimData24.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s7

theorem checked24_s8 : Seg.bok PrimData24.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s8

theorem checked24_s9 : Seg.bok PrimData24.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s9

theorem checked24_s10 : Seg.bok PrimData24.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s10

theorem checked24_s11 : Seg.bok PrimData24.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s11

theorem checked24_s12 : Seg.bok PrimData24.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s12

theorem checked24_s13 : Seg.bok PrimData24.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s13

theorem checked24_s14 : Seg.bok PrimData24.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s14

theorem checked24_s15 : Seg.bok PrimData24.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s15

theorem checked24_s16 : Seg.bok PrimData24.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s16

theorem checked24_s17 : Seg.bok PrimData24.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s17

theorem checked24_s18 : Seg.bok PrimData24.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s18

theorem checked24_s19 : Seg.bok PrimData24.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s19

theorem checked24_s20 : Seg.bok PrimData24.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s20

theorem checked24_s21 : Seg.bok PrimData24.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s21

theorem checked24_s22 : Seg.bok PrimData24.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s22

theorem checked24_s23 : Seg.bok PrimData24.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s23

theorem checked24_s24 : Seg.bok PrimData24.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s24

theorem checked24_s25 : Seg.bok PrimData24.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s25

theorem checked24_s26 : Seg.bok PrimData24.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s26

theorem checked24_s27 : Seg.bok PrimData24.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s27

theorem checked24_s28 : Seg.bok PrimData24.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s28

theorem checked24_s29 : Seg.bok PrimData24.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s29

theorem checked24_s30 : Seg.bok PrimData24.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s30

theorem checked24_s31 : Seg.bok PrimData24.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s31

theorem checked24_s32 : Seg.bok PrimData24.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s32

theorem checked24_s33 : Seg.bok PrimData24.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s33

theorem checked24_s34 : Seg.bok PrimData24.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24_s34

 theorem checked24 : ∀ s ∈ PrimData24.segs, (Seg.bok s) = true := by
  unfold PrimData24.segs
  exact List.forall_mem_cons.2 ⟨checked24_s0, List.forall_mem_cons.2 ⟨checked24_s1, List.forall_mem_cons.2 ⟨checked24_s2, List.forall_mem_cons.2 ⟨checked24_s3, List.forall_mem_cons.2 ⟨checked24_s4, List.forall_mem_cons.2 ⟨checked24_s5, List.forall_mem_cons.2 ⟨checked24_s6, List.forall_mem_cons.2 ⟨checked24_s7, List.forall_mem_cons.2 ⟨checked24_s8, List.forall_mem_cons.2 ⟨checked24_s9, List.forall_mem_cons.2 ⟨checked24_s10, List.forall_mem_cons.2 ⟨checked24_s11, List.forall_mem_cons.2 ⟨checked24_s12, List.forall_mem_cons.2 ⟨checked24_s13, List.forall_mem_cons.2 ⟨checked24_s14, List.forall_mem_cons.2 ⟨checked24_s15, List.forall_mem_cons.2 ⟨checked24_s16, List.forall_mem_cons.2 ⟨checked24_s17, List.forall_mem_cons.2 ⟨checked24_s18, List.forall_mem_cons.2 ⟨checked24_s19, List.forall_mem_cons.2 ⟨checked24_s20, List.forall_mem_cons.2 ⟨checked24_s21, List.forall_mem_cons.2 ⟨checked24_s22, List.forall_mem_cons.2 ⟨checked24_s23, List.forall_mem_cons.2 ⟨checked24_s24, List.forall_mem_cons.2 ⟨checked24_s25, List.forall_mem_cons.2 ⟨checked24_s26, List.forall_mem_cons.2 ⟨checked24_s27, List.forall_mem_cons.2 ⟨checked24_s28, List.forall_mem_cons.2 ⟨checked24_s29, List.forall_mem_cons.2 ⟨checked24_s30, List.forall_mem_cons.2 ⟨checked24_s31, List.forall_mem_cons.2 ⟨checked24_s32, List.forall_mem_cons.2 ⟨checked24_s33, List.forall_mem_singleton.2 checked24_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked24
