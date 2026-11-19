/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_45.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/4da47a2f-ba50-4fc1-8b26-df37ba856feb
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData45.s0 : Seg := ⟨435266803313129784806269825, 435266803313129793060377614, 23601155, 4096, [], 435415245871874150796842729, 435415245871874159053762601⟩
def PrimData45.s1 : Seg := ⟨435415245871874150796842729, 435415245871874159053762601, 23609347, 4096, [], 435569015483327165780533607, 435569015483327174040367692⟩
def PrimData45.s2 : Seg := ⟨435569015483327165780533607, 435569015483327174040367692, 23617539, 4096, [], 435720282800457891344538625, 435720282800457899607239619⟩
def PrimData45.s3 : Seg := ⟨435720282800457891344538625, 435720282800457899607239619, 23625731, 4096, [], 435874058674508017491610695, 435874058674508025757225921⟩
def PrimData45.s4 : Seg := ⟨435874058674508017491610695, 435874058674508025757225921, 23633923, 4096, [], 436021260617906884659545497, 436021260617906892927950587⟩
def PrimData45.s5 : Seg := ⟨436021260617906884659545497, 436021260617906892927950587, 23642115, 4096, [], 436166586328380422509636963, 436166586328380430780796506⟩
def PrimData45.s6 : Seg := ⟨436166586328380422509636963, 436166586328380430780796506, 23650307, 4096, [], 436321624415518822149498808, 436321624415518830423597307⟩
def PrimData45.s7 : Seg := ⟨436321624415518822149498808, 436321624415518830423597307, 23658499, 4096, [], 436480111064240899152224548, 436480111064240907429327665⟩
def PrimData45.s8 : Seg := ⟨436480111064240899152224548, 436480111064240907429327665, 23666691, 4096, [], 436628891096321593713299029, 436628891096321601993222752⟩
def PrimData45.s9 : Seg := ⟨436628891096321593713299029, 436628891096321601993222752, 23674883, 4096, [], 436780493169492213898668043, 436780493169492222181466456⟩
def PrimData45.s10 : Seg := ⟨436780493169492213898668043, 436780493169492222181466456, 23683075, 4096, [], 436931471909615345227136619, 436931471909615353512798294⟩
def PrimData45.s11 : Seg := ⟨436931471909615345227136619, 436931471909615353512798294, 23691267, 4096, [], 437082766982089457411679942, 437082766982089465700211064⟩
def PrimData45.s12 : Seg := ⟨437082766982089457411679942, 437082766982089465700211064, 23699459, 4096, [], 437231872375160695950226556, 437231872375160704241586321⟩
def PrimData45.s13 : Seg := ⟨437231872375160695950226556, 437231872375160704241586321, 23707651, 4096, [], 437378474789915551385329504, 437378474789915559679470870⟩
def PrimData45.s14 : Seg := ⟨437378474789915551385329504, 437378474789915559679470870, 23715843, 4096, [], 437527586287334096419501124, 437527586287334104716472352⟩
def PrimData45.s15 : Seg := ⟨437527586287334096419501124, 437527586287334104716472352, 23724035, 4096, [], 437677327322721081090472278, 437677327322721089390286204⟩
def PrimData45.s16 : Seg := ⟨437677327322721081090472278, 437677327322721089390286204, 23732227, 4096, [], 437824251967856347667990147, 437824251967856355970594072⟩
def PrimData45.s17 : Seg := ⟨437824251967856347667990147, 437824251967856355970594072, 23740419, 4096, [], 437978385025229546511567396, 437978385025229554817097886⟩
def PrimData45.s18 : Seg := ⟨437978385025229546511567396, 437978385025229554817097886, 23748611, 4096, [], 438127195386728447680086607, 438127195386728455988441359⟩
def PrimData45.s19 : Seg := ⟨438127195386728447680086607, 438127195386728455988441359, 23756803, 4096, [], 438281334687258013420405012, 438281334687258021731685600⟩
def PrimData45.s20 : Seg := ⟨438281334687258013420405012, 438281334687258021731685600, 23764995, 4096, [], 438429524443556908980269012, 438429524443556917294362441⟩
def PrimData45.s21 : Seg := ⟨438429524443556908980269012, 438429524443556917294362441, 23773187, 4096, [], 438585549810617946701436157, 438585549810617955018491629⟩
def PrimData45.s22 : Seg := ⟨438585549810617946701436157, 438585549810617955018491629, 23781379, 4096, [], 438734372191177516599479165, 438734372191177524919359385⟩
def PrimData45.s23 : Seg := ⟨438734372191177516599479165, 438734372191177524919359385, 23789571, 4096, [], 438883824225529700907126850, 438883824225529709229843968⟩
def PrimData45.s24 : Seg := ⟨438883824225529700907126850, 438883824225529709229843968, 23797763, 4096, [], 439036099227911075935334079, 439036099227911084260942041⟩
def PrimData45.s25 : Seg := ⟨439036099227911075935334079, 439036099227911084260942041, 23805955, 4096, [], 439185557356662214190735957, 439185557356662222519180088⟩
def PrimData45.s26 : Seg := ⟨439185557356662214190735957, 439185557356662222519180088, 23814147, 4096, [], 439339091895573094309194201, 439339091895573102640552747⟩
def PrimData45.s27 : Seg := ⟨439339091895573094309194201, 439339091895573102640552747, 23822339, 4096, [], 439489182679871319027573418, 439489182679871327361780769⟩
def PrimData45.s28 : Seg := ⟨439489182679871319027573418, 439489182679871327361780769, 23830531, 4096, [], 439632696263691619130387028, 439632696263691627467318282⟩
def PrimData45.s29 : Seg := ⟨439632696263691619130387028, 439632696263691627467318282, 23838723, 4096, [], 439785613353957361073055756, 439785613353957369412889032⟩
def PrimData45.s30 : Seg := ⟨439785613353957361073055756, 439785613353957369412889032, 23846915, 4096, [], 439927252608178656884324770, 439927252608178665226846228⟩
def PrimData45.s31 : Seg := ⟨439927252608178656884324770, 439927252608178665226846228, 23855107, 4096, [], 440077982332865686314028968, 440077982332865694659411381⟩
def PrimData45.s32 : Seg := ⟨440077982332865686314028968, 440077982332865694659411381, 23863299, 4096, [], 440234355813335953342583699, 440234355813335961690934473⟩
def PrimData45.s33 : Seg := ⟨440234355813335953342583699, 440234355813335961690934473, 23871491, 4096, [], 440384151505551104901158415, 440384151505551113252352405⟩
def PrimData45.s34 : Seg := ⟨440384151505551104901158415, 440384151505551113252352405, 23879683, 4096, [], 440536143894211984388836171, 440536143894211992742914444⟩

def PrimData45.segs : List Seg := [PrimData45.s0, PrimData45.s1, PrimData45.s2, PrimData45.s3, PrimData45.s4, PrimData45.s5, PrimData45.s6, PrimData45.s7, PrimData45.s8, PrimData45.s9, PrimData45.s10, PrimData45.s11, PrimData45.s12, PrimData45.s13, PrimData45.s14, PrimData45.s15, PrimData45.s16, PrimData45.s17, PrimData45.s18, PrimData45.s19, PrimData45.s20, PrimData45.s21, PrimData45.s22, PrimData45.s23, PrimData45.s24, PrimData45.s25, PrimData45.s26, PrimData45.s27, PrimData45.s28, PrimData45.s29, PrimData45.s30, PrimData45.s31, PrimData45.s32, PrimData45.s33, PrimData45.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked45_s0 : Seg.bok PrimData45.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s0

theorem checked45_s1 : Seg.bok PrimData45.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s1

theorem checked45_s2 : Seg.bok PrimData45.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s2

theorem checked45_s3 : Seg.bok PrimData45.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s3

theorem checked45_s4 : Seg.bok PrimData45.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s4

theorem checked45_s5 : Seg.bok PrimData45.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s5

theorem checked45_s6 : Seg.bok PrimData45.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s6

theorem checked45_s7 : Seg.bok PrimData45.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s7

theorem checked45_s8 : Seg.bok PrimData45.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s8

theorem checked45_s9 : Seg.bok PrimData45.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s9

theorem checked45_s10 : Seg.bok PrimData45.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s10

theorem checked45_s11 : Seg.bok PrimData45.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s11

theorem checked45_s12 : Seg.bok PrimData45.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s12

theorem checked45_s13 : Seg.bok PrimData45.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s13

theorem checked45_s14 : Seg.bok PrimData45.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s14

theorem checked45_s15 : Seg.bok PrimData45.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s15

theorem checked45_s16 : Seg.bok PrimData45.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s16

theorem checked45_s17 : Seg.bok PrimData45.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s17

theorem checked45_s18 : Seg.bok PrimData45.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s18

theorem checked45_s19 : Seg.bok PrimData45.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s19

theorem checked45_s20 : Seg.bok PrimData45.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s20

theorem checked45_s21 : Seg.bok PrimData45.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s21

theorem checked45_s22 : Seg.bok PrimData45.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s22

theorem checked45_s23 : Seg.bok PrimData45.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s23

theorem checked45_s24 : Seg.bok PrimData45.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s24

theorem checked45_s25 : Seg.bok PrimData45.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s25

theorem checked45_s26 : Seg.bok PrimData45.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s26

theorem checked45_s27 : Seg.bok PrimData45.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s27

theorem checked45_s28 : Seg.bok PrimData45.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s28

theorem checked45_s29 : Seg.bok PrimData45.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s29

theorem checked45_s30 : Seg.bok PrimData45.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s30

theorem checked45_s31 : Seg.bok PrimData45.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s31

theorem checked45_s32 : Seg.bok PrimData45.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s32

theorem checked45_s33 : Seg.bok PrimData45.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s33

theorem checked45_s34 : Seg.bok PrimData45.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45_s34

 theorem checked45 : ∀ s ∈ PrimData45.segs, (Seg.bok s) = true := by
  unfold PrimData45.segs
  exact List.forall_mem_cons.2 ⟨checked45_s0, List.forall_mem_cons.2 ⟨checked45_s1, List.forall_mem_cons.2 ⟨checked45_s2, List.forall_mem_cons.2 ⟨checked45_s3, List.forall_mem_cons.2 ⟨checked45_s4, List.forall_mem_cons.2 ⟨checked45_s5, List.forall_mem_cons.2 ⟨checked45_s6, List.forall_mem_cons.2 ⟨checked45_s7, List.forall_mem_cons.2 ⟨checked45_s8, List.forall_mem_cons.2 ⟨checked45_s9, List.forall_mem_cons.2 ⟨checked45_s10, List.forall_mem_cons.2 ⟨checked45_s11, List.forall_mem_cons.2 ⟨checked45_s12, List.forall_mem_cons.2 ⟨checked45_s13, List.forall_mem_cons.2 ⟨checked45_s14, List.forall_mem_cons.2 ⟨checked45_s15, List.forall_mem_cons.2 ⟨checked45_s16, List.forall_mem_cons.2 ⟨checked45_s17, List.forall_mem_cons.2 ⟨checked45_s18, List.forall_mem_cons.2 ⟨checked45_s19, List.forall_mem_cons.2 ⟨checked45_s20, List.forall_mem_cons.2 ⟨checked45_s21, List.forall_mem_cons.2 ⟨checked45_s22, List.forall_mem_cons.2 ⟨checked45_s23, List.forall_mem_cons.2 ⟨checked45_s24, List.forall_mem_cons.2 ⟨checked45_s25, List.forall_mem_cons.2 ⟨checked45_s26, List.forall_mem_cons.2 ⟨checked45_s27, List.forall_mem_cons.2 ⟨checked45_s28, List.forall_mem_cons.2 ⟨checked45_s29, List.forall_mem_cons.2 ⟨checked45_s30, List.forall_mem_cons.2 ⟨checked45_s31, List.forall_mem_cons.2 ⟨checked45_s32, List.forall_mem_cons.2 ⟨checked45_s33, List.forall_mem_singleton.2 checked45_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked45
