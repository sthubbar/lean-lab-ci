/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_26.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/9c1a65e2-67d5-4c63-8a98-d22bf7631ec9
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData26.s0 : Seg := ⟨334801085258342170523111720, 334801085258342176872076667, 18153475, 4096, [], 334949700321190025094061317, 334949700321190031445843864⟩
def PrimData26.s1 : Seg := ⟨334949700321190025094061317, 334949700321190031445843864, 18161667, 4096, [], 335094927676995178829719448, 335094927676995185184253775⟩
def PrimData26.s2 : Seg := ⟨335094927676995178829719448, 335094927676995185184253775, 18169859, 4096, [], 335250642655532531780409586, 335250642655532538137896211⟩
def PrimData26.s3 : Seg := ⟨335250642655532531780409586, 335250642655532538137896211, 18178051, 4096, [], 335392794189802837616920883, 335392794189802843977101077⟩
def PrimData26.s4 : Seg := ⟨335392794189802837616920883, 335392794189802843977101077, 18186243, 4096, [], 335544200557578811755401283, 335544200557578818118452393⟩
def PrimData26.s5 : Seg := ⟨335544200557578811755401283, 335544200557578818118452393, 18194435, 4096, [], 335691602118914134577399956, 335691602118914140943244362⟩
def PrimData26.s6 : Seg := ⟨335691602118914134577399956, 335691602118914140943244362, 18202627, 4096, [], 335840549537454546038424098, 335840549537454552407091926⟩
def PrimData26.s7 : Seg := ⟨335840549537454546038424098, 335840549537454552407091926, 18210819, 4096, [], 335995668709554234909793547, 335995668709554241281402274⟩
def PrimData26.s8 : Seg := ⟨335995668709554234909793547, 335995668709554241281402274, 18219011, 4096, [], 336145240862493767066876510, 336145240862493773441321346⟩
def PrimData26.s9 : Seg := ⟨336145240862493767066876510, 336145240862493773441321346, 18227203, 4096, [], 336303452441781151464693442, 336303452441781157842138314⟩
def PrimData26.s10 : Seg := ⟨336303452441781151464693442, 336303452441781157842138314, 18235395, 4096, [], 336466911255377225693379555, 336466911255377232073923895⟩
def PrimData26.s11 : Seg := ⟨336466911255377225693379555, 336466911255377232073923895, 18243587, 4096, [], 336612794473173056211473857, 336612794473173062594783239⟩
def PrimData26.s12 : Seg := ⟨336612794473173056211473857, 336612794473173062594783239, 18251779, 4096, [], 336765775485558003168050072, 336765775485558009554259837⟩
def PrimData26.s13 : Seg := ⟨336765775485558003168050072, 336765775485558009554259837, 18259971, 4096, [], 336924929380858689730724887, 336924929380858696119952462⟩
def PrimData26.s14 : Seg := ⟨336924929380858689730724887, 336924929380858696119952462, 18268163, 4096, [], 337073291949908596602476774, 337073291949908602994516981⟩
def PrimData26.s15 : Seg := ⟨337073291949908596602476774, 337073291949908602994516981, 18276355, 4096, [], 337228444465116250420539963, 337228444465116256815522383⟩
def PrimData26.s16 : Seg := ⟨337228444465116250420539963, 337228444465116256815522383, 18284547, 4096, [], 337378357304090301065764455, 337378357304090307463589429⟩
def PrimData26.s17 : Seg := ⟨337378357304090301065764455, 337378357304090307463589429, 18292739, 4096, [], 337529199487650276030777556, 337529199487650282431463392⟩
def PrimData26.s18 : Seg := ⟨337529199487650276030777556, 337529199487650282431463392, 18300931, 4096, [], 337685906955313765036152171, 337685906955313771439811280⟩
def PrimData26.s19 : Seg := ⟨337685906955313765036152171, 337685906955313771439811280, 18309123, 4096, [], 337837065785559831223580756, 337837065785559837630107193⟩
def PrimData26.s20 : Seg := ⟨337837065785559831223580756, 337837065785559837630107193, 18317315, 4096, [], 337994090072004377391354534, 337994090072004383800860549⟩
def PrimData26.s21 : Seg := ⟨337994090072004377391354534, 337994090072004383800860549, 18325507, 4096, [], 338144331423918376402847915, 338144331423918382815203081⟩
def PrimData26.s22 : Seg := ⟨338144331423918376402847915, 338144331423918382815203081, 18333699, 4096, [], 338291491662506516371945319, 338291491662506522787090561⟩
def PrimData26.s23 : Seg := ⟨338291491662506516371945319, 338291491662506522787090561, 18341891, 4096, [], 338438655821382625214878704, 338438655821382631632813828⟩
def PrimData26.s24 : Seg := ⟨338438655821382625214878704, 338438655821382631632813828, 18350083, 4096, [], 338586132412354301676523111, 338586132412354308097254184⟩
def PrimData26.s25 : Seg := ⟨338586132412354301676523111, 338586132412354308097254184, 18358275, 4096, [], 338730527657817813129110100, 338730527657817819552579502⟩
def PrimData26.s26 : Seg := ⟨338730527657817813129110100, 338730527657817819552579502, 18366467, 4096, [], 338882331778709940372153288, 338882331778709946798502003⟩
def PrimData26.s27 : Seg := ⟨338882331778709940372153288, 338882331778709946798502003, 18374659, 4096, [], 339035065651609533557480361, 339035065651609539986725747⟩
def PrimData26.s28 : Seg := ⟨339035065651609533557480361, 339035065651609539986725747, 18382851, 4096, [], 339183483725159005983042519, 339183483725159012415102793⟩
def PrimData26.s29 : Seg := ⟨339183483725159005983042519, 339183483725159012415102793, 18391043, 4096, [], 339335917206757798258014435, 339335917206757804692965594⟩
def PrimData26.s30 : Seg := ⟨339335917206757798258014435, 339335917206757804692965594, 18399235, 4096, [], 339489589032842315598883219, 339489589032842322036747444⟩
def PrimData26.s31 : Seg := ⟨339489589032842315598883219, 339489589032842322036747444, 18407427, 4096, [], 339644807856051876685190058, 339644807856051883125996455⟩
def PrimData26.s32 : Seg := ⟨339644807856051876685190058, 339644807856051883125996455, 18415619, 4096, [], 339791698688480367714488457, 339791698688480374158079946⟩
def PrimData26.s33 : Seg := ⟨339791698688480367714488457, 339791698688480374158079946, 18423811, 4096, [], 339938902115148633866224890, 339938902115148640312607142⟩
def PrimData26.s34 : Seg := ⟨339938902115148633866224890, 339938902115148640312607142, 18432003, 4096, [], 340094750587418127673812451, 340094750587418134123150337⟩

def PrimData26.segs : List Seg := [PrimData26.s0, PrimData26.s1, PrimData26.s2, PrimData26.s3, PrimData26.s4, PrimData26.s5, PrimData26.s6, PrimData26.s7, PrimData26.s8, PrimData26.s9, PrimData26.s10, PrimData26.s11, PrimData26.s12, PrimData26.s13, PrimData26.s14, PrimData26.s15, PrimData26.s16, PrimData26.s17, PrimData26.s18, PrimData26.s19, PrimData26.s20, PrimData26.s21, PrimData26.s22, PrimData26.s23, PrimData26.s24, PrimData26.s25, PrimData26.s26, PrimData26.s27, PrimData26.s28, PrimData26.s29, PrimData26.s30, PrimData26.s31, PrimData26.s32, PrimData26.s33, PrimData26.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked26_s0 : Seg.bok PrimData26.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s0

theorem checked26_s1 : Seg.bok PrimData26.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s1

theorem checked26_s2 : Seg.bok PrimData26.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s2

theorem checked26_s3 : Seg.bok PrimData26.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s3

theorem checked26_s4 : Seg.bok PrimData26.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s4

theorem checked26_s5 : Seg.bok PrimData26.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s5

theorem checked26_s6 : Seg.bok PrimData26.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s6

theorem checked26_s7 : Seg.bok PrimData26.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s7

theorem checked26_s8 : Seg.bok PrimData26.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s8

theorem checked26_s9 : Seg.bok PrimData26.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s9

theorem checked26_s10 : Seg.bok PrimData26.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s10

theorem checked26_s11 : Seg.bok PrimData26.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s11

theorem checked26_s12 : Seg.bok PrimData26.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s12

theorem checked26_s13 : Seg.bok PrimData26.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s13

theorem checked26_s14 : Seg.bok PrimData26.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s14

theorem checked26_s15 : Seg.bok PrimData26.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s15

theorem checked26_s16 : Seg.bok PrimData26.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s16

theorem checked26_s17 : Seg.bok PrimData26.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s17

theorem checked26_s18 : Seg.bok PrimData26.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s18

theorem checked26_s19 : Seg.bok PrimData26.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s19

theorem checked26_s20 : Seg.bok PrimData26.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s20

theorem checked26_s21 : Seg.bok PrimData26.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s21

theorem checked26_s22 : Seg.bok PrimData26.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s22

theorem checked26_s23 : Seg.bok PrimData26.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s23

theorem checked26_s24 : Seg.bok PrimData26.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s24

theorem checked26_s25 : Seg.bok PrimData26.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s25

theorem checked26_s26 : Seg.bok PrimData26.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s26

theorem checked26_s27 : Seg.bok PrimData26.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s27

theorem checked26_s28 : Seg.bok PrimData26.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s28

theorem checked26_s29 : Seg.bok PrimData26.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s29

theorem checked26_s30 : Seg.bok PrimData26.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s30

theorem checked26_s31 : Seg.bok PrimData26.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s31

theorem checked26_s32 : Seg.bok PrimData26.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s32

theorem checked26_s33 : Seg.bok PrimData26.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s33

theorem checked26_s34 : Seg.bok PrimData26.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26_s34

 theorem checked26 : ∀ s ∈ PrimData26.segs, (Seg.bok s) = true := by
  unfold PrimData26.segs
  exact List.forall_mem_cons.2 ⟨checked26_s0, List.forall_mem_cons.2 ⟨checked26_s1, List.forall_mem_cons.2 ⟨checked26_s2, List.forall_mem_cons.2 ⟨checked26_s3, List.forall_mem_cons.2 ⟨checked26_s4, List.forall_mem_cons.2 ⟨checked26_s5, List.forall_mem_cons.2 ⟨checked26_s6, List.forall_mem_cons.2 ⟨checked26_s7, List.forall_mem_cons.2 ⟨checked26_s8, List.forall_mem_cons.2 ⟨checked26_s9, List.forall_mem_cons.2 ⟨checked26_s10, List.forall_mem_cons.2 ⟨checked26_s11, List.forall_mem_cons.2 ⟨checked26_s12, List.forall_mem_cons.2 ⟨checked26_s13, List.forall_mem_cons.2 ⟨checked26_s14, List.forall_mem_cons.2 ⟨checked26_s15, List.forall_mem_cons.2 ⟨checked26_s16, List.forall_mem_cons.2 ⟨checked26_s17, List.forall_mem_cons.2 ⟨checked26_s18, List.forall_mem_cons.2 ⟨checked26_s19, List.forall_mem_cons.2 ⟨checked26_s20, List.forall_mem_cons.2 ⟨checked26_s21, List.forall_mem_cons.2 ⟨checked26_s22, List.forall_mem_cons.2 ⟨checked26_s23, List.forall_mem_cons.2 ⟨checked26_s24, List.forall_mem_cons.2 ⟨checked26_s25, List.forall_mem_cons.2 ⟨checked26_s26, List.forall_mem_cons.2 ⟨checked26_s27, List.forall_mem_cons.2 ⟨checked26_s28, List.forall_mem_cons.2 ⟨checked26_s29, List.forall_mem_cons.2 ⟨checked26_s30, List.forall_mem_cons.2 ⟨checked26_s31, List.forall_mem_cons.2 ⟨checked26_s32, List.forall_mem_cons.2 ⟨checked26_s33, List.forall_mem_singleton.2 checked26_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked26
