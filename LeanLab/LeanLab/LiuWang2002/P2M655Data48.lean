/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_48.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/6a2e4c01-486c-4555-81a0-6faf3aeaa6e7
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData48.s0 : Seg := ⟨451132359117069107816079277, 451132359117069116371116760, 24461315, 4096, [], 451284566718685491192308474, 451284566718685499750231640⟩
def PrimData48.s1 : Seg := ⟨451284566718685491192308474, 451284566718685499750231640, 24469507, 4096, [], 451440229624690992050694772, 451440229624691000611568749⟩
def PrimData48.s2 : Seg := ⟨451440229624690992050694772, 451440229624691000611568749, 24477699, 4096, [], 451593384807912606163799570, 451593384807912614727577320⟩
def PrimData48.s3 : Seg := ⟨451593384807912606163799570, 451593384807912614727577320, 24485891, 4096, [], 451742462920498787187269785, 451742462920498795753873391⟩
def PrimData48.s4 : Seg := ⟨451742462920498787187269785, 451742462920498795753873391, 24494083, 4096, [], 451894054854960011723838139, 451894054854960020293315252⟩
def PrimData48.s5 : Seg := ⟨451894054854960011723838139, 451894054854960020293315252, 24502275, 4096, [], 452048474510670034595718318, 452048474510670043168122016⟩
def PrimData48.s6 : Seg := ⟨452048474510670034595718318, 452048474510670043168122016, 24510467, 4096, [], 452196619853145212219766551, 452196619853145220794978847⟩
def PrimData48.s7 : Seg := ⟨452196619853145212219766551, 452196619853145220794978847, 24518659, 4096, [], 452349790095764318678131204, 452349790095764327256246894⟩
def PrimData48.s8 : Seg := ⟨452349790095764318678131204, 452349790095764327256246894, 24526851, 4096, [], 452502335590943300469186516, 452502335590943309050194092⟩
def PrimData48.s9 : Seg := ⟨452502335590943300469186516, 452502335590943309050194092, 24535043, 4096, [], 452651745187138623448402477, 452651745187138632032242848⟩
def PrimData48.s10 : Seg := ⟨452651745187138623448402477, 452651745187138632032242848, 24543235, 4096, [], 452810260578350960786988614, 452810260578350969373834325⟩
def PrimData48.s11 : Seg := ⟨452810260578350960786988614, 452810260578350969373834325, 24551427, 4096, [], 452955281438038853542601029, 452955281438038862132196046⟩
def PrimData48.s12 : Seg := ⟨452955281438038853542601029, 452955281438038862132196046, 24559619, 4096, [], 453104385901263189853133823, 453104385901263198445554962⟩
def PrimData48.s13 : Seg := ⟨453104385901263189853133823, 453104385901263198445554962, 24567811, 4096, [], 453261341109039398813258688, 453261341109039407408655224⟩
def PrimData48.s14 : Seg := ⟨453261341109039398813258688, 453261341109039407408655224, 24576003, 4096, [], 453407312249450876145948037, 453407312249450884744111756⟩
def PrimData48.s15 : Seg := ⟨453407312249450876145948037, 453407312249450884744111756, 24584195, 4096, [], 453558309023971896716554443, 453558309023971905317580399⟩
def PrimData48.s16 : Seg := ⟨453558309023971896716554443, 453558309023971905317580399, 24592387, 4096, [], 453708366992099232238965343, 453708366992099240842835936⟩
def PrimData48.s17 : Seg := ⟨453708366992099232238965343, 453708366992099240842835936, 24600579, 4096, [], 453852777040538403309100976, 453852777040538411915709121⟩
def PrimData48.s18 : Seg := ⟨453852777040538403309100976, 453852777040538411915709121, 24608771, 4096, [], 454006922110311413810332448, 454006922110311422419863051⟩
def PrimData48.s19 : Seg := ⟨454006922110311413810332448, 454006922110311422419863051, 24616963, 4096, [], 454158244705829527600937754, 454158244705829536213336552⟩
def PrimData48.s20 : Seg := ⟨454158244705829527600937754, 454158244705829536213336552, 24625155, 4096, [], 454312395764753706814634527, 454312395764753715429955755⟩
def PrimData48.s21 : Seg := ⟨454312395764753706814634527, 454312395764753715429955755, 24633347, 4096, [], 454458386945336694910128660, 454458386945336703528217190⟩
def PrimData48.s22 : Seg := ⟨454458386945336694910128660, 454458386945336703528217190, 24641539, 4096, [], 454608462465722234673127430, 454608462465722243294062311⟩
def PrimData48.s23 : Seg := ⟨454608462465722234673127430, 454608462465722243294062311, 24649731, 4096, [], 454761680713416290419716483, 454761680713416299043556308⟩
def PrimData48.s24 : Seg := ⟨454761680713416290419716483, 454761680713416299043556308, 24657923, 4096, [], 454909878280517920480964754, 454909878280517929107615291⟩
def PrimData48.s25 : Seg := ⟨454909878280517920480964754, 454909878280517929107615291, 24666115, 4096, [], 455067498228147800416797326, 455067498228147809046436978⟩
def PrimData48.s26 : Seg := ⟨455067498228147800416797326, 455067498228147809046436978, 24674307, 4096, [], 455223865285034624541616114, 455223865285034633174220820⟩
def PrimData48.s27 : Seg := ⟨455223865285034624541616114, 455223865285034633174220820, 24682499, 4096, [], 455384945348981924031481063, 455384945348981932667140947⟩
def PrimData48.s28 : Seg := ⟨455384945348981924031481063, 455384945348981932667140947, 24690691, 4096, [], 455532526476298029816942843, 455532526476298038455400656⟩
def PrimData48.s29 : Seg := ⟨455532526476298029816942843, 455532526476298038455400656, 24698883, 4096, [], 455683878568421925450162786, 455683878568421934091490916⟩
def PrimData48.s30 : Seg := ⟨455683878568421925450162786, 455683878568421934091490916, 24707075, 4096, [], 455842141930516660300136498, 455842141930516668944466410⟩
def PrimData48.s31 : Seg := ⟨455842141930516660300136498, 455842141930516668944466410, 24715267, 4096, [], 455996326162731949419378442, 455996326162731958066631290⟩
def PrimData48.s32 : Seg := ⟨455996326162731949419378442, 455996326162731958066631290, 24723459, 4096, [], 456145488910456020412070534, 456145488910456029062151427⟩
def PrimData48.s33 : Seg := ⟨456145488910456020412070534, 456145488910456029062151427, 24731651, 4096, [], 456288373896382385677113462, 456288373896382394329902494⟩
def PrimData48.s34 : Seg := ⟨456288373896382385677113462, 456288373896382394329902494, 24739843, 4096, [], 456440368808865448598245922, 456440368808865457253916777⟩

def PrimData48.segs : List Seg := [PrimData48.s0, PrimData48.s1, PrimData48.s2, PrimData48.s3, PrimData48.s4, PrimData48.s5, PrimData48.s6, PrimData48.s7, PrimData48.s8, PrimData48.s9, PrimData48.s10, PrimData48.s11, PrimData48.s12, PrimData48.s13, PrimData48.s14, PrimData48.s15, PrimData48.s16, PrimData48.s17, PrimData48.s18, PrimData48.s19, PrimData48.s20, PrimData48.s21, PrimData48.s22, PrimData48.s23, PrimData48.s24, PrimData48.s25, PrimData48.s26, PrimData48.s27, PrimData48.s28, PrimData48.s29, PrimData48.s30, PrimData48.s31, PrimData48.s32, PrimData48.s33, PrimData48.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked48_s0 : Seg.bok PrimData48.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s0

theorem checked48_s1 : Seg.bok PrimData48.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s1

theorem checked48_s2 : Seg.bok PrimData48.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s2

theorem checked48_s3 : Seg.bok PrimData48.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s3

theorem checked48_s4 : Seg.bok PrimData48.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s4

theorem checked48_s5 : Seg.bok PrimData48.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s5

theorem checked48_s6 : Seg.bok PrimData48.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s6

theorem checked48_s7 : Seg.bok PrimData48.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s7

theorem checked48_s8 : Seg.bok PrimData48.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s8

theorem checked48_s9 : Seg.bok PrimData48.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s9

theorem checked48_s10 : Seg.bok PrimData48.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s10

theorem checked48_s11 : Seg.bok PrimData48.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s11

theorem checked48_s12 : Seg.bok PrimData48.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s12

theorem checked48_s13 : Seg.bok PrimData48.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s13

theorem checked48_s14 : Seg.bok PrimData48.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s14

theorem checked48_s15 : Seg.bok PrimData48.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s15

theorem checked48_s16 : Seg.bok PrimData48.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s16

theorem checked48_s17 : Seg.bok PrimData48.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s17

theorem checked48_s18 : Seg.bok PrimData48.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s18

theorem checked48_s19 : Seg.bok PrimData48.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s19

theorem checked48_s20 : Seg.bok PrimData48.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s20

theorem checked48_s21 : Seg.bok PrimData48.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s21

theorem checked48_s22 : Seg.bok PrimData48.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s22

theorem checked48_s23 : Seg.bok PrimData48.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s23

theorem checked48_s24 : Seg.bok PrimData48.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s24

theorem checked48_s25 : Seg.bok PrimData48.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s25

theorem checked48_s26 : Seg.bok PrimData48.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s26

theorem checked48_s27 : Seg.bok PrimData48.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s27

theorem checked48_s28 : Seg.bok PrimData48.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s28

theorem checked48_s29 : Seg.bok PrimData48.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s29

theorem checked48_s30 : Seg.bok PrimData48.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s30

theorem checked48_s31 : Seg.bok PrimData48.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s31

theorem checked48_s32 : Seg.bok PrimData48.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s32

theorem checked48_s33 : Seg.bok PrimData48.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s33

theorem checked48_s34 : Seg.bok PrimData48.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48_s34

 theorem checked48 : ∀ s ∈ PrimData48.segs, (Seg.bok s) = true := by
  unfold PrimData48.segs
  exact List.forall_mem_cons.2 ⟨checked48_s0, List.forall_mem_cons.2 ⟨checked48_s1, List.forall_mem_cons.2 ⟨checked48_s2, List.forall_mem_cons.2 ⟨checked48_s3, List.forall_mem_cons.2 ⟨checked48_s4, List.forall_mem_cons.2 ⟨checked48_s5, List.forall_mem_cons.2 ⟨checked48_s6, List.forall_mem_cons.2 ⟨checked48_s7, List.forall_mem_cons.2 ⟨checked48_s8, List.forall_mem_cons.2 ⟨checked48_s9, List.forall_mem_cons.2 ⟨checked48_s10, List.forall_mem_cons.2 ⟨checked48_s11, List.forall_mem_cons.2 ⟨checked48_s12, List.forall_mem_cons.2 ⟨checked48_s13, List.forall_mem_cons.2 ⟨checked48_s14, List.forall_mem_cons.2 ⟨checked48_s15, List.forall_mem_cons.2 ⟨checked48_s16, List.forall_mem_cons.2 ⟨checked48_s17, List.forall_mem_cons.2 ⟨checked48_s18, List.forall_mem_cons.2 ⟨checked48_s19, List.forall_mem_cons.2 ⟨checked48_s20, List.forall_mem_cons.2 ⟨checked48_s21, List.forall_mem_cons.2 ⟨checked48_s22, List.forall_mem_cons.2 ⟨checked48_s23, List.forall_mem_cons.2 ⟨checked48_s24, List.forall_mem_cons.2 ⟨checked48_s25, List.forall_mem_cons.2 ⟨checked48_s26, List.forall_mem_cons.2 ⟨checked48_s27, List.forall_mem_cons.2 ⟨checked48_s28, List.forall_mem_cons.2 ⟨checked48_s29, List.forall_mem_cons.2 ⟨checked48_s30, List.forall_mem_cons.2 ⟨checked48_s31, List.forall_mem_cons.2 ⟨checked48_s32, List.forall_mem_cons.2 ⟨checked48_s33, List.forall_mem_singleton.2 checked48_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked48
