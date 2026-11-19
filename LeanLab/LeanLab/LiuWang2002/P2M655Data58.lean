/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_58.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/b6c395d1-ef65-4cd4-9ba0-0b5949944c23
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData58.s0 : Seg := ⟨504008332625792027011476429, 504008332625792036569189912, 27328515, 4096, [], 504159636527467711683407662, 504159636527467721243989465⟩
def PrimData58.s1 : Seg := ⟨504159636527467711683407662, 504159636527467721243989465, 27336707, 4096, [], 504310311265776735344920327, 504310311265776744908359228⟩
def PrimData58.s2 : Seg := ⟨504310311265776735344920327, 504310311265776744908359228, 27344899, 4096, [], 504463199868541646230370682, 504463199868541655796708483⟩
def PrimData58.s3 : Seg := ⟨504463199868541646230370682, 504463199868541655796708483, 27353091, 4096, [], 504617670617281382783814165, 504617670617281392353080880⟩
def PrimData58.s4 : Seg := ⟨504617670617281382783814165, 504617670617281392353080880, 27361283, 4096, [], 504764878451260108219100450, 504764878451260117791158479⟩
def PrimData58.s5 : Seg := ⟨504764878451260108219100450, 504764878451260117791158479, 27369475, 4096, [], 504907982158611686997117453, 504907982158611696571888553⟩
def PrimData58.s6 : Seg := ⟨504907982158611686997117453, 504907982158611696571888553, 27377667, 4096, [], 505064040526238257025651464, 505064040526238266603381508⟩
def PrimData58.s7 : Seg := ⟨505064040526238257025651464, 505064040526238266603381508, 27385859, 4096, [], 505215994793071184568806334, 505215994793071194149417316⟩
def PrimData58.s8 : Seg := ⟨505215994793071184568806334, 505215994793071194149417316, 27394051, 4096, [], 505367635730377879196498444, 505367635730377888779984801⟩
def PrimData58.s9 : Seg := ⟨505367635730377879196498444, 505367635730377888779984801, 27402243, 4096, [], 505520543033332393324877742, 505520543033332402911263527⟩
def PrimData58.s10 : Seg := ⟨505520543033332393324877742, 505520543033332402911263527, 27410435, 4096, [], 505670925579428487575154412, 505670925579428497164391382⟩
def PrimData58.s11 : Seg := ⟨505670925579428487575154412, 505670925579428497164391382, 27418627, 4096, [], 505822890389855170184438816, 505822890389855179776557482⟩
def PrimData58.s12 : Seg := ⟨505822890389855170184438816, 505822890389855179776557482, 27426819, 4096, [], 505981492605955445800670612, 505981492605955455395796132⟩
def PrimData58.s13 : Seg := ⟨505981492605955445800670612, 505981492605955455395796132, 27435011, 4096, [], 506139149822893672958354991, 506139149822893682556470346⟩
def PrimData58.s14 : Seg := ⟨506139149822893672958354991, 506139149822893682556470346, 27443203, 4096, [], 506284803573007399012925376, 506284803573007408613803535⟩
def PrimData58.s15 : Seg := ⟨506284803573007399012925376, 506284803573007408613803535, 27451395, 4096, [], 506430459862355792698463211, 506430459862355802302103036⟩
def PrimData58.s16 : Seg := ⟨506430459862355792698463211, 506430459862355802302103036, 27459587, 4096, [], 506582753921834086919536370, 506582753921834096526063748⟩
def PrimData58.s17 : Seg := ⟨506582753921834086919536370, 506582753921834096526063748, 27467779, 4096, [], 506734102705227576206820808, 506734102705227585816218059⟩
def PrimData58.s18 : Seg := ⟨506734102705227576206820808, 506734102705227585816218059, 27475971, 4096, [], 506880082576068778034308466, 506880082576068787646473315⟩
def PrimData58.s19 : Seg := ⟨506880082576068778034308466, 506880082576068787646473315, 27484163, 4096, [], 507033964482720099176965003, 507033964482720108792048381⟩
def PrimData58.s20 : Seg := ⟨507033964482720099176965003, 507033964482720108792048381, 27492355, 4096, [], 507174577684075021733044292, 507174577684075031350794151⟩
def PrimData58.s21 : Seg := ⟨507174577684075021733044292, 507174577684075031350794151, 27500547, 4096, [], 507330360879625618488786229, 507330360879625628109490745⟩
def PrimData58.s22 : Seg := ⟨507330360879625618488786229, 507330360879625628109490745, 27508739, 4096, [], 507484882802070167000641435, 507484882802070176624277147⟩
def PrimData58.s23 : Seg := ⟨507484882802070167000641435, 507484882802070176624277147, 27516931, 4096, [], 507637827393003783355652681, 507637827393003792982189717⟩
def PrimData58.s24 : Seg := ⟨507637827393003783355652681, 507637827393003792982189717, 27525123, 4096, [], 507786350542683134959607113, 507786350542683144588961615⟩
def PrimData58.s25 : Seg := ⟨507786350542683134959607113, 507786350542683144588961615, 27533315, 4096, [], 507939616461598438339841195, 507939616461598447972103077⟩
def PrimData58.s26 : Seg := ⟨507939616461598438339841195, 507939616461598447972103077, 27541507, 4096, [], 508091620951902335568781638, 508091620951902345203927085⟩
def PrimData58.s27 : Seg := ⟨508091620951902335568781638, 508091620951902345203927085, 27549699, 4096, [], 508242680013225271544358303, 508242680013225281182369822⟩
def PrimData58.s28 : Seg := ⟨508242680013225271544358303, 508242680013225281182369822, 27557891, 4096, [], 508396585980135039230893170, 508396585980135048871824230⟩
def PrimData58.s29 : Seg := ⟨508396585980135039230893170, 508396585980135048871824230, 27566083, 4096, [], 508547018239964561252238098, 508547018239964570896022833⟩
def PrimData58.s30 : Seg := ⟨508547018239964561252238098, 508547018239964570896022833, 27574275, 4096, [], 508700297482612217383112604, 508700297482612227029804723⟩
def PrimData58.s31 : Seg := ⟨508700297482612217383112604, 508700297482612227029804723, 27582467, 4096, [], 508858320018855065082082010, 508858320018855074731771427⟩
def PrimData58.s32 : Seg := ⟨508858320018855065082082010, 508858320018855074731771427, 27590659, 4096, [], 509014765062565609688614548, 509014765062565619341271871⟩
def PrimData58.s33 : Seg := ⟨509014765062565609688614548, 509014765062565619341271871, 27598851, 4096, [], 509175637558491755023369842, 509175637558491764679078902⟩
def PrimData58.s34 : Seg := ⟨509175637558491755023369842, 509175637558491764679078902, 27607043, 4096, [], 509314388563109653985733884, 509314388563109663644073328⟩

def PrimData58.segs : List Seg := [PrimData58.s0, PrimData58.s1, PrimData58.s2, PrimData58.s3, PrimData58.s4, PrimData58.s5, PrimData58.s6, PrimData58.s7, PrimData58.s8, PrimData58.s9, PrimData58.s10, PrimData58.s11, PrimData58.s12, PrimData58.s13, PrimData58.s14, PrimData58.s15, PrimData58.s16, PrimData58.s17, PrimData58.s18, PrimData58.s19, PrimData58.s20, PrimData58.s21, PrimData58.s22, PrimData58.s23, PrimData58.s24, PrimData58.s25, PrimData58.s26, PrimData58.s27, PrimData58.s28, PrimData58.s29, PrimData58.s30, PrimData58.s31, PrimData58.s32, PrimData58.s33, PrimData58.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked58_s0 : Seg.bok PrimData58.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s0

theorem checked58_s1 : Seg.bok PrimData58.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s1

theorem checked58_s2 : Seg.bok PrimData58.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s2

theorem checked58_s3 : Seg.bok PrimData58.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s3

theorem checked58_s4 : Seg.bok PrimData58.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s4

theorem checked58_s5 : Seg.bok PrimData58.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s5

theorem checked58_s6 : Seg.bok PrimData58.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s6

theorem checked58_s7 : Seg.bok PrimData58.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s7

theorem checked58_s8 : Seg.bok PrimData58.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s8

theorem checked58_s9 : Seg.bok PrimData58.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s9

theorem checked58_s10 : Seg.bok PrimData58.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s10

theorem checked58_s11 : Seg.bok PrimData58.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s11

theorem checked58_s12 : Seg.bok PrimData58.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s12

theorem checked58_s13 : Seg.bok PrimData58.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s13

theorem checked58_s14 : Seg.bok PrimData58.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s14

theorem checked58_s15 : Seg.bok PrimData58.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s15

theorem checked58_s16 : Seg.bok PrimData58.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s16

theorem checked58_s17 : Seg.bok PrimData58.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s17

theorem checked58_s18 : Seg.bok PrimData58.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s18

theorem checked58_s19 : Seg.bok PrimData58.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s19

theorem checked58_s20 : Seg.bok PrimData58.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s20

theorem checked58_s21 : Seg.bok PrimData58.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s21

theorem checked58_s22 : Seg.bok PrimData58.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s22

theorem checked58_s23 : Seg.bok PrimData58.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s23

theorem checked58_s24 : Seg.bok PrimData58.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s24

theorem checked58_s25 : Seg.bok PrimData58.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s25

theorem checked58_s26 : Seg.bok PrimData58.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s26

theorem checked58_s27 : Seg.bok PrimData58.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s27

theorem checked58_s28 : Seg.bok PrimData58.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s28

theorem checked58_s29 : Seg.bok PrimData58.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s29

theorem checked58_s30 : Seg.bok PrimData58.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s30

theorem checked58_s31 : Seg.bok PrimData58.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s31

theorem checked58_s32 : Seg.bok PrimData58.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s32

theorem checked58_s33 : Seg.bok PrimData58.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s33

theorem checked58_s34 : Seg.bok PrimData58.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58_s34

 theorem checked58 : ∀ s ∈ PrimData58.segs, (Seg.bok s) = true := by
  unfold PrimData58.segs
  exact List.forall_mem_cons.2 ⟨checked58_s0, List.forall_mem_cons.2 ⟨checked58_s1, List.forall_mem_cons.2 ⟨checked58_s2, List.forall_mem_cons.2 ⟨checked58_s3, List.forall_mem_cons.2 ⟨checked58_s4, List.forall_mem_cons.2 ⟨checked58_s5, List.forall_mem_cons.2 ⟨checked58_s6, List.forall_mem_cons.2 ⟨checked58_s7, List.forall_mem_cons.2 ⟨checked58_s8, List.forall_mem_cons.2 ⟨checked58_s9, List.forall_mem_cons.2 ⟨checked58_s10, List.forall_mem_cons.2 ⟨checked58_s11, List.forall_mem_cons.2 ⟨checked58_s12, List.forall_mem_cons.2 ⟨checked58_s13, List.forall_mem_cons.2 ⟨checked58_s14, List.forall_mem_cons.2 ⟨checked58_s15, List.forall_mem_cons.2 ⟨checked58_s16, List.forall_mem_cons.2 ⟨checked58_s17, List.forall_mem_cons.2 ⟨checked58_s18, List.forall_mem_cons.2 ⟨checked58_s19, List.forall_mem_cons.2 ⟨checked58_s20, List.forall_mem_cons.2 ⟨checked58_s21, List.forall_mem_cons.2 ⟨checked58_s22, List.forall_mem_cons.2 ⟨checked58_s23, List.forall_mem_cons.2 ⟨checked58_s24, List.forall_mem_cons.2 ⟨checked58_s25, List.forall_mem_cons.2 ⟨checked58_s26, List.forall_mem_cons.2 ⟨checked58_s27, List.forall_mem_cons.2 ⟨checked58_s28, List.forall_mem_cons.2 ⟨checked58_s29, List.forall_mem_cons.2 ⟨checked58_s30, List.forall_mem_cons.2 ⟨checked58_s31, List.forall_mem_cons.2 ⟨checked58_s32, List.forall_mem_cons.2 ⟨checked58_s33, List.forall_mem_singleton.2 checked58_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked58
