/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_20.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/67a6fccb-17bd-4e92-bf92-35b954901df1
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData20.s0 : Seg := ⟨303038931286996925069001588, 303038931286996930815622342, 16433155, 4096, [], 303194630094727822123639913, 303194630094727827873208897⟩
def PrimData20.s1 : Seg := ⟨303194630094727822123639913, 303194630094727827873208897, 16441347, 4096, [], 303345123073058619811371081, 303345123073058625563789137⟩
def PrimData20.s2 : Seg := ⟨303345123073058619811371081, 303345123073058625563789137, 16449539, 4096, [], 303486118711085946174998052, 303486118711085951930084440⟩
def PrimData20.s3 : Seg := ⟨303486118711085946174998052, 303486118711085951930084440, 16457731, 4096, [], 303638153296069553348253594, 303638153296069559106218232⟩
def PrimData20.s4 : Seg := ⟨303638153296069553348253594, 303638153296069559106218232, 16465923, 4096, [], 303791418553079482686666402, 303791418553079488447532636⟩
def PrimData20.s5 : Seg := ⟨303791418553079482686666402, 303791418553079488447532636, 16474115, 4096, [], 303943768731616517488490551, 303943768731616523252240906⟩
def PrimData20.s6 : Seg := ⟨303943768731616517488490551, 303943768731616523252240906, 16482307, 4096, [], 304100415253556831847499266, 304100415253556837614215428⟩
def PrimData20.s7 : Seg := ⟨304100415253556831847499266, 304100415253556837614215428, 16490499, 4096, [], 304251854880047519169881161, 304251854880047524939463945⟩
def PrimData20.s8 : Seg := ⟨304251854880047519169881161, 304251854880047524939463945, 16498691, 4096, [], 304404525310013403913302003, 304404525310013409685774732⟩
def PrimData20.s9 : Seg := ⟨304404525310013403913302003, 304404525310013409685774732, 16506883, 4096, [], 304555360850483965098652908, 304555360850483970873980628⟩
def PrimData20.s10 : Seg := ⟨304555360850483965098652908, 304555360850483970873980628, 16515075, 4096, [], 304700988994175747783295176, 304700988994175753561378819⟩
def PrimData20.s11 : Seg := ⟨304700988994175747783295176, 304700988994175753561378819, 16523267, 4096, [], 304852446708871373643439979, 304852446708871379424390321⟩
def PrimData20.s12 : Seg := ⟨304852446708871373643439979, 304852446708871379424390321, 16531459, 4096, [], 305001762755215150610740274, 305001762755215156394516455⟩
def PrimData20.s13 : Seg := ⟨305001762755215150610740274, 305001762755215156394516455, 16539651, 4096, [], 305148323638625605976132736, 305148323638625611762682391⟩
def PrimData20.s14 : Seg := ⟨305148323638625605976132736, 305148323638625611762682391, 16547843, 4096, [], 305295808871194129054366021, 305295808871194134843706660⟩
def PrimData20.s15 : Seg := ⟨305295808871194129054366021, 305295808871194134843706660, 16556035, 4096, [], 305446364787265698361702384, 305446364787265704153892241⟩
def PrimData20.s16 : Seg := ⟨305446364787265698361702384, 305446364787265704153892241, 16564227, 4096, [], 305597845066289696819611190, 305597845066289702614667790⟩
def PrimData20.s17 : Seg := ⟨305597845066289696819611190, 305597845066289702614667790, 16572419, 4096, [], 305744730239367469526938839, 305744730239367475324774980⟩
def PrimData20.s18 : Seg := ⟨305744730239367469526938839, 305744730239367475324774980, 16580611, 4096, [], 305899899452545225450492116, 305899899452545231251265114⟩
def PrimData20.s19 : Seg := ⟨305899899452545225450492116, 305899899452545231251265114, 16588803, 4096, [], 306057526585840727081414395, 306057526585840732885170950⟩
def PrimData20.s20 : Seg := ⟨306057526585840727081414395, 306057526585840732885170950, 16596995, 4096, [], 306209331569675819292767203, 306209331569675825099396584⟩
def PrimData20.s21 : Seg := ⟨306209331569675819292767203, 306209331569675825099396584, 16605187, 4096, [], 306363901208341191497756578, 306363901208341197307311428⟩
def PrimData20.s22 : Seg := ⟨306363901208341191497756578, 306363901208341197307311428, 16613379, 4096, [], 306519395552446839074035436, 306519395552446844886533275⟩
def PrimData20.s23 : Seg := ⟨306519395552446839074035436, 306519395552446844886533275, 16621571, 4096, [], 306662319642005923801590715, 306662319642005929616792771⟩
def PrimData20.s24 : Seg := ⟨306662319642005923801590715, 306662319642005929616792771, 16629763, 4096, [], 306813835894413701243363191, 306813835894413707061432699⟩
def PrimData20.s25 : Seg := ⟨306813835894413701243363191, 306813835894413707061432699, 16637955, 4096, [], 306966890245919726308200813, 306966890245919732129167031⟩
def PrimData20.s26 : Seg := ⟨306966890245919726308200813, 306966890245919732129167031, 16646147, 4096, [], 307122096296843202079788217, 307122096296843207903692051⟩
def PrimData20.s27 : Seg := ⟨307122096296843202079788217, 307122096296843207903692051, 16654339, 4096, [], 307271172061337109654844148, 307271172061337115481569377⟩
def PrimData20.s28 : Seg := ⟨307271172061337109654844148, 307271172061337115481569377, 16662531, 4096, [], 307423013057127582219613576, 307423013057127588049212872⟩
def PrimData20.s29 : Seg := ⟨307423013057127582219613576, 307423013057127588049212872, 16670723, 4096, [], 307574551758360939062145091, 307574551758360944894612816⟩
def PrimData20.s30 : Seg := ⟨307574551758360939062145091, 307574551758360944894612816, 16678915, 4096, [], 307724867851821832774507359, 307724867851821838609820536⟩
def PrimData20.s31 : Seg := ⟨307724867851821832774507359, 307724867851821838609820536, 16687107, 4096, [], 307878562910569205863302413, 307878562910569211701525466⟩
def PrimData20.s32 : Seg := ⟨307878562910569205863302413, 307878562910569211701525466, 16695299, 4096, [], 308023365787359694300115380, 308023365787359700141080164⟩
def PrimData20.s33 : Seg := ⟨308023365787359694300115380, 308023365787359700141080164, 16703491, 4096, [], 308174308806582347620484107, 308174308806582353464307447⟩
def PrimData20.s34 : Seg := ⟨308174308806582347620484107, 308174308806582353464307447, 16711683, 4096, [], 308325563039865186934554257, 308325563039865192781242494⟩

def PrimData20.segs : List Seg := [PrimData20.s0, PrimData20.s1, PrimData20.s2, PrimData20.s3, PrimData20.s4, PrimData20.s5, PrimData20.s6, PrimData20.s7, PrimData20.s8, PrimData20.s9, PrimData20.s10, PrimData20.s11, PrimData20.s12, PrimData20.s13, PrimData20.s14, PrimData20.s15, PrimData20.s16, PrimData20.s17, PrimData20.s18, PrimData20.s19, PrimData20.s20, PrimData20.s21, PrimData20.s22, PrimData20.s23, PrimData20.s24, PrimData20.s25, PrimData20.s26, PrimData20.s27, PrimData20.s28, PrimData20.s29, PrimData20.s30, PrimData20.s31, PrimData20.s32, PrimData20.s33, PrimData20.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked20_s0 : Seg.bok PrimData20.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s0

theorem checked20_s1 : Seg.bok PrimData20.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s1

theorem checked20_s2 : Seg.bok PrimData20.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s2

theorem checked20_s3 : Seg.bok PrimData20.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s3

theorem checked20_s4 : Seg.bok PrimData20.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s4

theorem checked20_s5 : Seg.bok PrimData20.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s5

theorem checked20_s6 : Seg.bok PrimData20.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s6

theorem checked20_s7 : Seg.bok PrimData20.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s7

theorem checked20_s8 : Seg.bok PrimData20.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s8

theorem checked20_s9 : Seg.bok PrimData20.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s9

theorem checked20_s10 : Seg.bok PrimData20.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s10

theorem checked20_s11 : Seg.bok PrimData20.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s11

theorem checked20_s12 : Seg.bok PrimData20.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s12

theorem checked20_s13 : Seg.bok PrimData20.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s13

theorem checked20_s14 : Seg.bok PrimData20.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s14

theorem checked20_s15 : Seg.bok PrimData20.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s15

theorem checked20_s16 : Seg.bok PrimData20.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s16

theorem checked20_s17 : Seg.bok PrimData20.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s17

theorem checked20_s18 : Seg.bok PrimData20.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s18

theorem checked20_s19 : Seg.bok PrimData20.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s19

theorem checked20_s20 : Seg.bok PrimData20.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s20

theorem checked20_s21 : Seg.bok PrimData20.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s21

theorem checked20_s22 : Seg.bok PrimData20.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s22

theorem checked20_s23 : Seg.bok PrimData20.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s23

theorem checked20_s24 : Seg.bok PrimData20.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s24

theorem checked20_s25 : Seg.bok PrimData20.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s25

theorem checked20_s26 : Seg.bok PrimData20.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s26

theorem checked20_s27 : Seg.bok PrimData20.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s27

theorem checked20_s28 : Seg.bok PrimData20.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s28

theorem checked20_s29 : Seg.bok PrimData20.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s29

theorem checked20_s30 : Seg.bok PrimData20.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s30

theorem checked20_s31 : Seg.bok PrimData20.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s31

theorem checked20_s32 : Seg.bok PrimData20.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s32

theorem checked20_s33 : Seg.bok PrimData20.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s33

theorem checked20_s34 : Seg.bok PrimData20.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20_s34

 theorem checked20 : ∀ s ∈ PrimData20.segs, (Seg.bok s) = true := by
  unfold PrimData20.segs
  exact List.forall_mem_cons.2 ⟨checked20_s0, List.forall_mem_cons.2 ⟨checked20_s1, List.forall_mem_cons.2 ⟨checked20_s2, List.forall_mem_cons.2 ⟨checked20_s3, List.forall_mem_cons.2 ⟨checked20_s4, List.forall_mem_cons.2 ⟨checked20_s5, List.forall_mem_cons.2 ⟨checked20_s6, List.forall_mem_cons.2 ⟨checked20_s7, List.forall_mem_cons.2 ⟨checked20_s8, List.forall_mem_cons.2 ⟨checked20_s9, List.forall_mem_cons.2 ⟨checked20_s10, List.forall_mem_cons.2 ⟨checked20_s11, List.forall_mem_cons.2 ⟨checked20_s12, List.forall_mem_cons.2 ⟨checked20_s13, List.forall_mem_cons.2 ⟨checked20_s14, List.forall_mem_cons.2 ⟨checked20_s15, List.forall_mem_cons.2 ⟨checked20_s16, List.forall_mem_cons.2 ⟨checked20_s17, List.forall_mem_cons.2 ⟨checked20_s18, List.forall_mem_cons.2 ⟨checked20_s19, List.forall_mem_cons.2 ⟨checked20_s20, List.forall_mem_cons.2 ⟨checked20_s21, List.forall_mem_cons.2 ⟨checked20_s22, List.forall_mem_cons.2 ⟨checked20_s23, List.forall_mem_cons.2 ⟨checked20_s24, List.forall_mem_cons.2 ⟨checked20_s25, List.forall_mem_cons.2 ⟨checked20_s26, List.forall_mem_cons.2 ⟨checked20_s27, List.forall_mem_cons.2 ⟨checked20_s28, List.forall_mem_cons.2 ⟨checked20_s29, List.forall_mem_cons.2 ⟨checked20_s30, List.forall_mem_cons.2 ⟨checked20_s31, List.forall_mem_cons.2 ⟨checked20_s32, List.forall_mem_cons.2 ⟨checked20_s33, List.forall_mem_singleton.2 checked20_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked20
