/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_29.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/1297226e-a7a0-43fc-8854-4d7d9d0411fc
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData29.s0 : Seg := ⟨350664342769958929402594830, 350664342769958936052401021, 19013635, 4096, [], 350811204974219572172322377, 350811204974219578824913322⟩
def PrimData29.s1 : Seg := ⟨350811204974219572172322377, 350811204974219578824913322, 19021827, 4096, [], 350961781327755027328828446, 350961781327755033984274495⟩
def PrimData29.s2 : Seg := ⟨350961781327755027328828446, 350961781327755033984274495, 19030019, 4096, [], 351116071890517881641224348, 351116071890517888299596583⟩
def PrimData29.s3 : Seg := ⟨351116071890517881641224348, 351116071890517888299596583, 19038211, 4096, [], 351268511177397052068472214, 351268511177397058729735374⟩
def PrimData29.s4 : Seg := ⟨351268511177397052068472214, 351268511177397058729735374, 19046403, 4096, [], 351420335922815715413042072, 351420335922815722077184015⟩
def PrimData29.s5 : Seg := ⟨351420335922815715413042072, 351420335922815722077184015, 19054595, 4096, [], 351569690786201698243206498, 351569690786201704910180079⟩
def PrimData29.s6 : Seg := ⟨351569690786201698243206498, 351569690786201704910180079, 19062787, 4096, [], 351715338779527257763413967, 351715338779527264433149458⟩
def PrimData29.s7 : Seg := ⟨351715338779527257763413967, 351715338779527264433149458, 19070979, 4096, [], 351869958365797408447350263, 351869958365797415120018539⟩
def PrimData29.s8 : Seg := ⟨351869958365797408447350263, 351869958365797415120018539, 19079171, 4096, [], 352024581968324777494998426, 352024581968324784170598939⟩
def PrimData29.s9 : Seg := ⟨352024581968324777494998426, 352024581968324784170598939, 19087363, 4096, [], 352173333641533155034146552, 352173333641533161712567394⟩
def PrimData29.s10 : Seg := ⟨352173333641533155034146552, 352173333641533161712567394, 19095555, 4096, [], 352316831629438658185022279, 352316831629438664866163802⟩
def PrimData29.s11 : Seg := ⟨352316831629438658185022279, 352316831629438664866163802, 19103747, 4096, [], 352463735253006738675575823, 352463735253006745359502967⟩
def PrimData29.s12 : Seg := ⟨352463735253006738675575823, 352463735253006745359502967, 19111939, 4096, [], 352620230370918936382273785, 352620230370918943069168024⟩
def PrimData29.s13 : Seg := ⟨352620230370918936382273785, 352620230370918943069168024, 19120131, 4096, [], 352771780796611767693058495, 352771780796611774382825834⟩
def PrimData29.s14 : Seg := ⟨352771780796611767693058495, 352771780796611774382825834, 19128323, 4096, [], 352928593246343443644477907, 352928593246343450337218527⟩
def PrimData29.s15 : Seg := ⟨352928593246343443644477907, 352928593246343450337218527, 19136515, 4096, [], 353075511968683119589223414, 353075511968683126284749703⟩
def PrimData29.s16 : Seg := ⟨353075511968683119589223414, 353075511968683126284749703, 19144707, 4096, [], 353226146131437208861851837, 353226146131437215560235078⟩
def PrimData29.s17 : Seg := ⟨353226146131437208861851837, 353226146131437215560235078, 19152899, 4096, [], 353383279840240336009930029, 353383279840240342711292476⟩
def PrimData29.s18 : Seg := ⟨353383279840240336009930029, 353383279840240342711292476, 19161091, 4096, [], 353530519150531979166150009, 353530519150531985870304369⟩
def PrimData29.s19 : Seg := ⟨353530519150531979166150009, 353530519150531985870304369, 19169283, 4096, [], 353675287460954759917027738, 353675287460954766623926563⟩
def PrimData29.s20 : Seg := ⟨353675287460954759917027738, 353675287460954766623926563, 19177475, 4096, [], 353827483697238462060324567, 353827483697238468770109452⟩
def PrimData29.s21 : Seg := ⟨353827483697238462060324567, 353827483697238468770109452, 19185667, 4096, [], 353980921196950680896221567, 353980921196950687608916303⟩
def PrimData29.s22 : Seg := ⟨353980921196950680896221567, 353980921196950687608916303, 19193859, 4096, [], 354138384292673771898569889, 354138384292673778614251337⟩
def PrimData29.s23 : Seg := ⟨354138384292673771898569889, 354138384292673778614251337, 19202051, 4096, [], 354276361282514946022711864, 354276361282514952741009329⟩
def PrimData29.s24 : Seg := ⟨354276361282514946022711864, 354276361282514952741009329, 19210243, 4096, [], 354427335447661968335168993, 354427335447661975056328881⟩
def PrimData29.s25 : Seg := ⟨354427335447661968335168993, 354427335447661975056328881, 19218435, 4096, [], 354581716747832011436604219, 354581716747832018160691476⟩
def PrimData29.s26 : Seg := ⟨354581716747832011436604219, 354581716747832018160691476, 19226627, 4096, [], 354729295394513730210871465, 354729295394513736937757756⟩
def PrimData29.s27 : Seg := ⟨354729295394513730210871465, 354729295394513736937757756, 19234819, 4096, [], 354878115364045616243478669, 354878115364045622973187252⟩
def PrimData29.s28 : Seg := ⟨354878115364045616243478669, 354878115364045622973187252, 19243011, 4096, [], 355032198969533685968855306, 355032198969533692701485736⟩
def PrimData29.s29 : Seg := ⟨355032198969533685968855306, 355032198969533692701485736, 19251203, 4096, [], 355189071241434562020472816, 355189071241434568756079420⟩
def PrimData29.s30 : Seg := ⟨355189071241434562020472816, 355189071241434568756079420, 19259395, 4096, [], 355336355417647128029777779, 355336355417647134768178632⟩
def PrimData29.s31 : Seg := ⟨355336355417647128029777779, 355336355417647134768178632, 19267587, 4096, [], 355485190464834248695129407, 355485190464834255436353810⟩
def PrimData29.s32 : Seg := ⟨355485190464834248695129407, 355485190464834255436353810, 19275779, 4096, [], 355637123641008446267186912, 355637123641008453011292925⟩
def PrimData29.s33 : Seg := ⟨355637123641008446267186912, 355637123641008453011292925, 19283971, 4096, [], 355786894618908940874046379, 355786894618908947620992692⟩
def PrimData29.s34 : Seg := ⟨355786894618908940874046379, 355786894618908947620992692, 19292163, 4096, [], 355935122081115487807741748, 355935122081115494557499687⟩

def PrimData29.segs : List Seg := [PrimData29.s0, PrimData29.s1, PrimData29.s2, PrimData29.s3, PrimData29.s4, PrimData29.s5, PrimData29.s6, PrimData29.s7, PrimData29.s8, PrimData29.s9, PrimData29.s10, PrimData29.s11, PrimData29.s12, PrimData29.s13, PrimData29.s14, PrimData29.s15, PrimData29.s16, PrimData29.s17, PrimData29.s18, PrimData29.s19, PrimData29.s20, PrimData29.s21, PrimData29.s22, PrimData29.s23, PrimData29.s24, PrimData29.s25, PrimData29.s26, PrimData29.s27, PrimData29.s28, PrimData29.s29, PrimData29.s30, PrimData29.s31, PrimData29.s32, PrimData29.s33, PrimData29.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked29_s0 : Seg.bok PrimData29.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s0

theorem checked29_s1 : Seg.bok PrimData29.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s1

theorem checked29_s2 : Seg.bok PrimData29.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s2

theorem checked29_s3 : Seg.bok PrimData29.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s3

theorem checked29_s4 : Seg.bok PrimData29.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s4

theorem checked29_s5 : Seg.bok PrimData29.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s5

theorem checked29_s6 : Seg.bok PrimData29.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s6

theorem checked29_s7 : Seg.bok PrimData29.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s7

theorem checked29_s8 : Seg.bok PrimData29.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s8

theorem checked29_s9 : Seg.bok PrimData29.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s9

theorem checked29_s10 : Seg.bok PrimData29.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s10

theorem checked29_s11 : Seg.bok PrimData29.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s11

theorem checked29_s12 : Seg.bok PrimData29.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s12

theorem checked29_s13 : Seg.bok PrimData29.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s13

theorem checked29_s14 : Seg.bok PrimData29.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s14

theorem checked29_s15 : Seg.bok PrimData29.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s15

theorem checked29_s16 : Seg.bok PrimData29.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s16

theorem checked29_s17 : Seg.bok PrimData29.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s17

theorem checked29_s18 : Seg.bok PrimData29.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s18

theorem checked29_s19 : Seg.bok PrimData29.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s19

theorem checked29_s20 : Seg.bok PrimData29.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s20

theorem checked29_s21 : Seg.bok PrimData29.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s21

theorem checked29_s22 : Seg.bok PrimData29.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s22

theorem checked29_s23 : Seg.bok PrimData29.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s23

theorem checked29_s24 : Seg.bok PrimData29.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s24

theorem checked29_s25 : Seg.bok PrimData29.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s25

theorem checked29_s26 : Seg.bok PrimData29.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s26

theorem checked29_s27 : Seg.bok PrimData29.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s27

theorem checked29_s28 : Seg.bok PrimData29.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s28

theorem checked29_s29 : Seg.bok PrimData29.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s29

theorem checked29_s30 : Seg.bok PrimData29.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s30

theorem checked29_s31 : Seg.bok PrimData29.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s31

theorem checked29_s32 : Seg.bok PrimData29.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s32

theorem checked29_s33 : Seg.bok PrimData29.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s33

theorem checked29_s34 : Seg.bok PrimData29.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29_s34

 theorem checked29 : ∀ s ∈ PrimData29.segs, (Seg.bok s) = true := by
  unfold PrimData29.segs
  exact List.forall_mem_cons.2 ⟨checked29_s0, List.forall_mem_cons.2 ⟨checked29_s1, List.forall_mem_cons.2 ⟨checked29_s2, List.forall_mem_cons.2 ⟨checked29_s3, List.forall_mem_cons.2 ⟨checked29_s4, List.forall_mem_cons.2 ⟨checked29_s5, List.forall_mem_cons.2 ⟨checked29_s6, List.forall_mem_cons.2 ⟨checked29_s7, List.forall_mem_cons.2 ⟨checked29_s8, List.forall_mem_cons.2 ⟨checked29_s9, List.forall_mem_cons.2 ⟨checked29_s10, List.forall_mem_cons.2 ⟨checked29_s11, List.forall_mem_cons.2 ⟨checked29_s12, List.forall_mem_cons.2 ⟨checked29_s13, List.forall_mem_cons.2 ⟨checked29_s14, List.forall_mem_cons.2 ⟨checked29_s15, List.forall_mem_cons.2 ⟨checked29_s16, List.forall_mem_cons.2 ⟨checked29_s17, List.forall_mem_cons.2 ⟨checked29_s18, List.forall_mem_cons.2 ⟨checked29_s19, List.forall_mem_cons.2 ⟨checked29_s20, List.forall_mem_cons.2 ⟨checked29_s21, List.forall_mem_cons.2 ⟨checked29_s22, List.forall_mem_cons.2 ⟨checked29_s23, List.forall_mem_cons.2 ⟨checked29_s24, List.forall_mem_cons.2 ⟨checked29_s25, List.forall_mem_cons.2 ⟨checked29_s26, List.forall_mem_cons.2 ⟨checked29_s27, List.forall_mem_cons.2 ⟨checked29_s28, List.forall_mem_cons.2 ⟨checked29_s29, List.forall_mem_cons.2 ⟨checked29_s30, List.forall_mem_cons.2 ⟨checked29_s31, List.forall_mem_cons.2 ⟨checked29_s32, List.forall_mem_cons.2 ⟨checked29_s33, List.forall_mem_singleton.2 checked29_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked29
