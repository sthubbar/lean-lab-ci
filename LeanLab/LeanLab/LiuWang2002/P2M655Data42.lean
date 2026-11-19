/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_42.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/48d4efc4-64e3-4e31-8171-f7db4bb9250f
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData42.s0 : Seg := ⟨419402124588824740579115472, 419402124588824748532434272, 22740995, 4096, [], 419551180078186465458442993, 419551180078186473414588529⟩
def PrimData42.s1 : Seg := ⟨419551180078186465458442993, 419551180078186473414588529, 22749187, 4096, [], 419700551190183973616569622, 419700551190183981575547952⟩
def PrimData42.s2 : Seg := ⟨419700551190183973616569622, 419700551190183981575547952, 22757379, 4096, [], 419851800434893297574912282, 419851800434893305536759096⟩
def PrimData42.s3 : Seg := ⟨419851800434893297574912282, 419851800434893305536759096, 22765571, 4096, [], 419999927880697204264081994, 419999927880697212228737865⟩
def PrimData42.s4 : Seg := ⟨419999927880697204264081994, 419999927880697212228737865, 22773763, 4096, [], 420152121154093155367224449, 420152121154093163334767236⟩
def PrimData42.s5 : Seg := ⟨420152121154093155367224449, 420152121154093163334767236, 22781955, 4096, [], 420303692641282588642401887, 420303692641282596612819118⟩
def PrimData42.s6 : Seg := ⟨420303692641282588642401887, 420303692641282596612819118, 22790147, 4096, [], 420447766707508555164912679, 420447766707508563138062050⟩
def PrimData42.s7 : Seg := ⟨420447766707508555164912679, 420447766707508563138062050, 22798339, 4096, [], 420597781937459127671416963, 420597781937459135647412212⟩
def PrimData42.s8 : Seg := ⟨420597781937459127671416963, 420597781937459135647412212, 22806531, 4096, [], 420749363018274483866000717, 420749363018274491844869947⟩
def PrimData42.s9 : Seg := ⟨420749363018274483866000717, 420749363018274491844869947, 22814723, 4096, [], 420896884255754813122447581, 420896884255754821104115158⟩
def PrimData42.s10 : Seg := ⟨420896884255754813122447581, 420896884255754821104115158, 22822915, 4096, [], 421044408580493281648031618, 421044408580493289632497939⟩
def PrimData42.s11 : Seg := ⟨421044408580493281648031618, 421044408580493289632497939, 22831107, 4096, [], 421195374170409872714234003, 421195374170409880701563744⟩
def PrimData42.s12 : Seg := ⟨421195374170409872714234003, 421195374170409880701563744, 22839299, 4096, [], 421356345031527320735475861, 421356345031527328725860006⟩
def PrimData42.s13 : Seg := ⟨421356345031527320735475861, 421356345031527328725860006, 22847491, 4096, [], 421510130163333387975846427, 421510130163333395969148174⟩
def PrimData42.s14 : Seg := ⟨421510130163333387975846427, 421510130163333395969148174, 22855683, 4096, [], 421660792779353648118871094, 421660792779353656115030666⟩
def PrimData42.s15 : Seg := ⟨421660792779353648118871094, 421660792779353656115030666, 22863875, 4096, [], 421813334081999659149071718, 421813334081999667148125128⟩
def PrimData42.s16 : Seg := ⟨421813334081999659149071718, 421813334081999667148125128, 22872067, 4096, [], 421962752730625649983280088, 421962752730625657985168036⟩
def PrimData42.s17 : Seg := ⟨421962752730625649983280088, 421962752730625657985168036, 22880259, 4096, [], 422118113869452460950497224, 422118113869452468955332253⟩
def PrimData42.s18 : Seg := ⟨422118113869452460950497224, 422118113869452468955332253, 22888451, 4096, [], 422271602716191390274432797, 422271602716191398282179186⟩
def PrimData42.s19 : Seg := ⟨422271602716191390274432797, 422271602716191398282179186, 22896643, 4096, [], 422420405574788887603819607, 422420405574788895614387919⟩
def PrimData42.s20 : Seg := ⟨422420405574788887603819607, 422420405574788895614387919, 22904835, 4096, [], 422569211562515074349057377, 422569211562515082362447501⟩
def PrimData42.s21 : Seg := ⟨422569211562515074349057377, 422569211562515082362447501, 22913027, 4096, [], 422726774131726521104698255, 422726774131726529121076643⟩
def PrimData42.s22 : Seg := ⟨422726774131726521104698255, 422726774131726529121076643, 22921219, 4096, [], 422879963282852637482822854, 422879963282852645502106755⟩
def PrimData42.s23 : Seg := ⟨422879963282852637482822854, 422879963282852645502106755, 22929411, 4096, [], 423029091399027160207587649, 423029091399027168229699665⟩
def PrimData42.s24 : Seg := ⟨423029091399027160207587649, 423029091399027168229699665, 22937603, 4096, [], 423174158232917337539125100, 423174158232917345563988556⟩
def PrimData42.s25 : Seg := ⟨423174158232917337539125100, 423174158232917345563988556, 22945795, 4096, [], 423327044376827739289753408, 423327044376827747317517568⟩
def PrimData42.s26 : Seg := ⟨423327044376827739289753408, 423327044376827747317517568, 22953987, 4096, [], 423477745172585925007425682, 423477745172585933038048600⟩
def PrimData42.s27 : Seg := ⟨423477745172585925007425682, 423477745172585933038048600, 22962179, 4096, [], 423627511153565310287055966, 423627511153565318320519626⟩
def PrimData42.s28 : Seg := ⟨423627511153565310287055966, 423627511153565318320519626, 22970371, 4096, [], 423776654893547722941882265, 423776654893547730978175859⟩
def PrimData42.s29 : Seg := ⟨423776654893547722941882265, 423776654893547730978175859, 22978563, 4096, [], 423929866580552903046817359, 423929866580552911086017049⟩
def PrimData42.s30 : Seg := ⟨423929866580552903046817359, 423929866580552911086017049, 22986755, 4096, [], 424079954731198788191273798, 424079954731198796233320569⟩
def PrimData42.s31 : Seg := ⟨424079954731198788191273798, 424079954731198796233320569, 22994947, 4096, [], 424234736355304976923739016, 424234736355304984968721841⟩
def PrimData42.s32 : Seg := ⟨424234736355304976923739016, 424234736355304984968721841, 23003139, 4096, [], 424391710064470906932594209, 424391710064470914980555145⟩
def PrimData42.s33 : Seg := ⟨424391710064470906932594209, 424391710064470914980555145, 23011331, 4096, [], 424546185476733693177221284, 424546185476733701228112188⟩
def PrimData42.s34 : Seg := ⟨424546185476733693177221284, 424546185476733701228112188, 23019523, 4096, [], 424700351423881678638417722, 424700351423881686692232531⟩

def PrimData42.segs : List Seg := [PrimData42.s0, PrimData42.s1, PrimData42.s2, PrimData42.s3, PrimData42.s4, PrimData42.s5, PrimData42.s6, PrimData42.s7, PrimData42.s8, PrimData42.s9, PrimData42.s10, PrimData42.s11, PrimData42.s12, PrimData42.s13, PrimData42.s14, PrimData42.s15, PrimData42.s16, PrimData42.s17, PrimData42.s18, PrimData42.s19, PrimData42.s20, PrimData42.s21, PrimData42.s22, PrimData42.s23, PrimData42.s24, PrimData42.s25, PrimData42.s26, PrimData42.s27, PrimData42.s28, PrimData42.s29, PrimData42.s30, PrimData42.s31, PrimData42.s32, PrimData42.s33, PrimData42.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked42_s0 : Seg.bok PrimData42.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s0

theorem checked42_s1 : Seg.bok PrimData42.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s1

theorem checked42_s2 : Seg.bok PrimData42.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s2

theorem checked42_s3 : Seg.bok PrimData42.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s3

theorem checked42_s4 : Seg.bok PrimData42.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s4

theorem checked42_s5 : Seg.bok PrimData42.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s5

theorem checked42_s6 : Seg.bok PrimData42.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s6

theorem checked42_s7 : Seg.bok PrimData42.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s7

theorem checked42_s8 : Seg.bok PrimData42.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s8

theorem checked42_s9 : Seg.bok PrimData42.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s9

theorem checked42_s10 : Seg.bok PrimData42.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s10

theorem checked42_s11 : Seg.bok PrimData42.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s11

theorem checked42_s12 : Seg.bok PrimData42.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s12

theorem checked42_s13 : Seg.bok PrimData42.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s13

theorem checked42_s14 : Seg.bok PrimData42.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s14

theorem checked42_s15 : Seg.bok PrimData42.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s15

theorem checked42_s16 : Seg.bok PrimData42.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s16

theorem checked42_s17 : Seg.bok PrimData42.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s17

theorem checked42_s18 : Seg.bok PrimData42.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s18

theorem checked42_s19 : Seg.bok PrimData42.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s19

theorem checked42_s20 : Seg.bok PrimData42.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s20

theorem checked42_s21 : Seg.bok PrimData42.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s21

theorem checked42_s22 : Seg.bok PrimData42.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s22

theorem checked42_s23 : Seg.bok PrimData42.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s23

theorem checked42_s24 : Seg.bok PrimData42.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s24

theorem checked42_s25 : Seg.bok PrimData42.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s25

theorem checked42_s26 : Seg.bok PrimData42.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s26

theorem checked42_s27 : Seg.bok PrimData42.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s27

theorem checked42_s28 : Seg.bok PrimData42.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s28

theorem checked42_s29 : Seg.bok PrimData42.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s29

theorem checked42_s30 : Seg.bok PrimData42.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s30

theorem checked42_s31 : Seg.bok PrimData42.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s31

theorem checked42_s32 : Seg.bok PrimData42.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s32

theorem checked42_s33 : Seg.bok PrimData42.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s33

theorem checked42_s34 : Seg.bok PrimData42.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42_s34

 theorem checked42 : ∀ s ∈ PrimData42.segs, (Seg.bok s) = true := by
  unfold PrimData42.segs
  exact List.forall_mem_cons.2 ⟨checked42_s0, List.forall_mem_cons.2 ⟨checked42_s1, List.forall_mem_cons.2 ⟨checked42_s2, List.forall_mem_cons.2 ⟨checked42_s3, List.forall_mem_cons.2 ⟨checked42_s4, List.forall_mem_cons.2 ⟨checked42_s5, List.forall_mem_cons.2 ⟨checked42_s6, List.forall_mem_cons.2 ⟨checked42_s7, List.forall_mem_cons.2 ⟨checked42_s8, List.forall_mem_cons.2 ⟨checked42_s9, List.forall_mem_cons.2 ⟨checked42_s10, List.forall_mem_cons.2 ⟨checked42_s11, List.forall_mem_cons.2 ⟨checked42_s12, List.forall_mem_cons.2 ⟨checked42_s13, List.forall_mem_cons.2 ⟨checked42_s14, List.forall_mem_cons.2 ⟨checked42_s15, List.forall_mem_cons.2 ⟨checked42_s16, List.forall_mem_cons.2 ⟨checked42_s17, List.forall_mem_cons.2 ⟨checked42_s18, List.forall_mem_cons.2 ⟨checked42_s19, List.forall_mem_cons.2 ⟨checked42_s20, List.forall_mem_cons.2 ⟨checked42_s21, List.forall_mem_cons.2 ⟨checked42_s22, List.forall_mem_cons.2 ⟨checked42_s23, List.forall_mem_cons.2 ⟨checked42_s24, List.forall_mem_cons.2 ⟨checked42_s25, List.forall_mem_cons.2 ⟨checked42_s26, List.forall_mem_cons.2 ⟨checked42_s27, List.forall_mem_cons.2 ⟨checked42_s28, List.forall_mem_cons.2 ⟨checked42_s29, List.forall_mem_cons.2 ⟨checked42_s30, List.forall_mem_cons.2 ⟨checked42_s31, List.forall_mem_cons.2 ⟨checked42_s32, List.forall_mem_cons.2 ⟨checked42_s33, List.forall_mem_singleton.2 checked42_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked42
