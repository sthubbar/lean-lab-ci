/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_31.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/5afbe728-d5cf-4751-8e48-40fdc6583f4f
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData31.s0 : Seg := ⟨361210244834022073443681811, 361210244834022080293475875, 19587075, 4096, [], 361364181498865263818363879, 361364181498865270671078211⟩
def PrimData31.s1 : Seg := ⟨361364181498865263818363879, 361364181498865270671078211, 19595267, 4096, [], 361518431687052239813462852, 361518431687052246669102858⟩
def PrimData31.s2 : Seg := ⟨361518431687052239813462852, 361518431687052246669102858, 19603459, 4096, [], 361674544173440431723398687, 361674544173440438581999797⟩
def PrimData31.s3 : Seg := ⟨361674544173440431723398687, 361674544173440438581999797, 19611651, 4096, [], 361829421686628175185850702, 361829421686628182047389814⟩
def PrimData31.s4 : Seg := ⟨361829421686628175185850702, 361829421686628182047389814, 19619843, 4096, [], 361982754182570714051333559, 361982754182570720915781983⟩
def PrimData31.s5 : Seg := ⟨361982754182570714051333559, 361982754182570720915781983, 19628035, 4096, [], 362130204797916291757586103, 362130204797916298624830681⟩
def PrimData31.s6 : Seg := ⟨362130204797916291757586103, 362130204797916298624830681, 19636227, 4096, [], 362277349275729168062147714, 362277349275729174932184502⟩
def PrimData31.s7 : Seg := ⟨362277349275729168062147714, 362277349275729174932184502, 19644419, 4096, [], 362426665941227475824869506, 362426665941227482697737695⟩
def PrimData31.s8 : Seg := ⟨362426665941227475824869506, 362426665941227482697737695, 19652611, 4096, [], 362577225475390565359564827, 362577225475390572235288019⟩
def PrimData31.s9 : Seg := ⟨362577225475390565359564827, 362577225475390572235288019, 19660803, 4096, [], 362732126030214743588459444, 362732126030214750467120666⟩
def PrimData31.s10 : Seg := ⟨362732126030214743588459444, 362732126030214750467120666, 19668995, 4096, [], 362878355727276067547679799, 362878355727276074429114282⟩
def PrimData31.s11 : Seg := ⟨362878355727276067547679799, 362878355727276074429114282, 19677187, 4096, [], 363028926457785765025762021, 363028926457785771910051166⟩
def PrimData31.s12 : Seg := ⟨363028926457785765025762021, 363028926457785771910051166, 19685379, 4096, [], 363181050054140562355500312, 363181050054140569242674054⟩
def PrimData31.s13 : Seg := ⟨363181050054140562355500312, 363181050054140569242674054, 19693571, 4096, [], 363337515038803134518916589, 363337515038803141409057309⟩
def PrimData31.s14 : Seg := ⟨363337515038803134518916589, 363337515038803141409057309, 19701763, 4096, [], 363493054431382726374317860, 363493054431382733267407805⟩
def PrimData31.s15 : Seg := ⟨363493054431382726374317860, 363493054431382733267407805, 19709955, 4096, [], 363643640072428660152372815, 363643640072428667048317475⟩
def PrimData31.s16 : Seg := ⟨363643640072428660152372815, 363643640072428667048317475, 19718147, 4096, [], 363790511248843112929384038, 363790511248843119828113393⟩
def PrimData31.s17 : Seg := ⟨363790511248843112929384038, 363790511248843119828113393, 19726339, 4096, [], 363938005760282994365599485, 363938005760283001267124818⟩
def PrimData31.s18 : Seg := ⟨363938005760282994365599485, 363938005760283001267124818, 19734531, 4096, [], 364090151943719426491154903, 364090151943719433395564382⟩
def PrimData31.s19 : Seg := ⟨364090151943719426491154903, 364090151943719433395564382, 19742723, 4096, [], 364245710496477927493926267, 364245710496477934401285579⟩
def PrimData31.s20 : Seg := ⟨364245710496477927493926267, 364245710496477934401285579, 19750915, 4096, [], 364397864165759716783816579, 364397864165759723694060064⟩
def PrimData31.s21 : Seg := ⟨364397864165759716783816579, 364397864165759723694060064, 19759107, 4096, [], 364552190883165217953180429, 364552190883165224866349956⟩
def PrimData31.s22 : Seg := ⟨364552190883165217953180429, 364552190883165224866349956, 19767299, 4096, [], 364705591708406003938883837, 364705591708406010854962144⟩
def PrimData31.s23 : Seg := ⟨364705591708406003938883837, 364705591708406010854962144, 19775491, 4096, [], 364850938722193785411238559, 364850938722193792330072127⟩
def PrimData31.s24 : Seg := ⟨364850938722193785411238559, 364850938722193792330072127, 19783683, 4096, [], 365007136337682094097746602, 365007136337682101019542450⟩
def PrimData31.s25 : Seg := ⟨365007136337682094097746602, 365007136337682101019542450, 19791875, 4096, [], 365162098099436793820242354, 365162098099436800744976416⟩
def PrimData31.s26 : Seg := ⟨365162098099436793820242354, 365162098099436800744976416, 19800067, 4096, [], 365315204033470821563254453, 365315204033470828490891103⟩
def PrimData31.s27 : Seg := ⟨365315204033470821563254453, 365315204033470828490891103, 19808259, 4096, [], 365464594483190354275956434, 365464594483190361206425708⟩
def PrimData31.s28 : Seg := ⟨365464594483190354275956434, 365464594483190361206425708, 19816451, 4096, [], 365618947841104648476050868, 365618947841104655409446834⟩
def PrimData31.s29 : Seg := ⟨365618947841104648476050868, 365618947841104655409446834, 19824643, 4096, [], 365766795902671036167202782, 365766795902671043103401478⟩
def PrimData31.s30 : Seg := ⟨365766795902671036167202782, 365766795902671043103401478, 19832835, 4096, [], 365910618089460883829096945, 365910618089460890768021703⟩
def PrimData31.s31 : Seg := ⟨365910618089460883829096945, 365910618089460890768021703, 19841027, 4096, [], 366070252229314402570677598, 366070252229314409512629865⟩
def PrimData31.s32 : Seg := ⟨366070252229314402570677598, 366070252229314409512629865, 19849219, 4096, [], 366224000758598339893569197, 366224000758598346838436383⟩
def PrimData31.s33 : Seg := ⟨366224000758598339893569197, 366224000758598346838436383, 19857411, 4096, [], 366372793325937453842788999, 366372793325937460790477161⟩
def PrimData31.s34 : Seg := ⟨366372793325937453842788999, 366372793325937460790477161, 19865603, 4096, [], 366523449551318007454215586, 366523449551318014404759915⟩

def PrimData31.segs : List Seg := [PrimData31.s0, PrimData31.s1, PrimData31.s2, PrimData31.s3, PrimData31.s4, PrimData31.s5, PrimData31.s6, PrimData31.s7, PrimData31.s8, PrimData31.s9, PrimData31.s10, PrimData31.s11, PrimData31.s12, PrimData31.s13, PrimData31.s14, PrimData31.s15, PrimData31.s16, PrimData31.s17, PrimData31.s18, PrimData31.s19, PrimData31.s20, PrimData31.s21, PrimData31.s22, PrimData31.s23, PrimData31.s24, PrimData31.s25, PrimData31.s26, PrimData31.s27, PrimData31.s28, PrimData31.s29, PrimData31.s30, PrimData31.s31, PrimData31.s32, PrimData31.s33, PrimData31.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked31_s0 : Seg.bok PrimData31.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s0

theorem checked31_s1 : Seg.bok PrimData31.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s1

theorem checked31_s2 : Seg.bok PrimData31.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s2

theorem checked31_s3 : Seg.bok PrimData31.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s3

theorem checked31_s4 : Seg.bok PrimData31.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s4

theorem checked31_s5 : Seg.bok PrimData31.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s5

theorem checked31_s6 : Seg.bok PrimData31.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s6

theorem checked31_s7 : Seg.bok PrimData31.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s7

theorem checked31_s8 : Seg.bok PrimData31.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s8

theorem checked31_s9 : Seg.bok PrimData31.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s9

theorem checked31_s10 : Seg.bok PrimData31.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s10

theorem checked31_s11 : Seg.bok PrimData31.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s11

theorem checked31_s12 : Seg.bok PrimData31.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s12

theorem checked31_s13 : Seg.bok PrimData31.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s13

theorem checked31_s14 : Seg.bok PrimData31.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s14

theorem checked31_s15 : Seg.bok PrimData31.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s15

theorem checked31_s16 : Seg.bok PrimData31.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s16

theorem checked31_s17 : Seg.bok PrimData31.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s17

theorem checked31_s18 : Seg.bok PrimData31.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s18

theorem checked31_s19 : Seg.bok PrimData31.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s19

theorem checked31_s20 : Seg.bok PrimData31.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s20

theorem checked31_s21 : Seg.bok PrimData31.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s21

theorem checked31_s22 : Seg.bok PrimData31.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s22

theorem checked31_s23 : Seg.bok PrimData31.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s23

theorem checked31_s24 : Seg.bok PrimData31.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s24

theorem checked31_s25 : Seg.bok PrimData31.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s25

theorem checked31_s26 : Seg.bok PrimData31.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s26

theorem checked31_s27 : Seg.bok PrimData31.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s27

theorem checked31_s28 : Seg.bok PrimData31.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s28

theorem checked31_s29 : Seg.bok PrimData31.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s29

theorem checked31_s30 : Seg.bok PrimData31.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s30

theorem checked31_s31 : Seg.bok PrimData31.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s31

theorem checked31_s32 : Seg.bok PrimData31.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s32

theorem checked31_s33 : Seg.bok PrimData31.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s33

theorem checked31_s34 : Seg.bok PrimData31.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31_s34

 theorem checked31 : ∀ s ∈ PrimData31.segs, (Seg.bok s) = true := by
  unfold PrimData31.segs
  exact List.forall_mem_cons.2 ⟨checked31_s0, List.forall_mem_cons.2 ⟨checked31_s1, List.forall_mem_cons.2 ⟨checked31_s2, List.forall_mem_cons.2 ⟨checked31_s3, List.forall_mem_cons.2 ⟨checked31_s4, List.forall_mem_cons.2 ⟨checked31_s5, List.forall_mem_cons.2 ⟨checked31_s6, List.forall_mem_cons.2 ⟨checked31_s7, List.forall_mem_cons.2 ⟨checked31_s8, List.forall_mem_cons.2 ⟨checked31_s9, List.forall_mem_cons.2 ⟨checked31_s10, List.forall_mem_cons.2 ⟨checked31_s11, List.forall_mem_cons.2 ⟨checked31_s12, List.forall_mem_cons.2 ⟨checked31_s13, List.forall_mem_cons.2 ⟨checked31_s14, List.forall_mem_cons.2 ⟨checked31_s15, List.forall_mem_cons.2 ⟨checked31_s16, List.forall_mem_cons.2 ⟨checked31_s17, List.forall_mem_cons.2 ⟨checked31_s18, List.forall_mem_cons.2 ⟨checked31_s19, List.forall_mem_cons.2 ⟨checked31_s20, List.forall_mem_cons.2 ⟨checked31_s21, List.forall_mem_cons.2 ⟨checked31_s22, List.forall_mem_cons.2 ⟨checked31_s23, List.forall_mem_cons.2 ⟨checked31_s24, List.forall_mem_cons.2 ⟨checked31_s25, List.forall_mem_cons.2 ⟨checked31_s26, List.forall_mem_cons.2 ⟨checked31_s27, List.forall_mem_cons.2 ⟨checked31_s28, List.forall_mem_cons.2 ⟨checked31_s29, List.forall_mem_cons.2 ⟨checked31_s30, List.forall_mem_cons.2 ⟨checked31_s31, List.forall_mem_cons.2 ⟨checked31_s32, List.forall_mem_cons.2 ⟨checked31_s33, List.forall_mem_singleton.2 checked31_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked31
