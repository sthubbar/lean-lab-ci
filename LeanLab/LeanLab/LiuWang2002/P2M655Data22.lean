/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_22.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/675fc697-36dd-447b-9338-378f7ec18c1e
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData22.s0 : Seg := ⟨313641899375288204660420084, 313641899375288210608101811, 17006595, 4096, [], 313798226607399871543972193, 313798226607399877494623496⟩
def PrimData22.s1 : Seg := ⟨313798226607399871543972193, 313798226607399877494623496, 17014787, 4096, [], 313947494292852740926857808, 313947494292852746880344551⟩
def PrimData22.s2 : Seg := ⟨313947494292852740926857808, 313947494292852746880344551, 17022979, 4096, [], 314105366348747741978452078, 314105366348747747934937557⟩
def PrimData22.s3 : Seg := ⟨314105366348747741978452078, 314105366348747747934937557, 17031171, 4096, [], 314253414083621969120115769, 314253414083621975079413360⟩
def PrimData22.s4 : Seg := ⟨314253414083621969120115769, 314253414083621975079413360, 17039363, 4096, [], 314402080433895861042314660, 314402080433895867004436027⟩
def PrimData22.s5 : Seg := ⟨314402080433895861042314660, 314402080433895867004436027, 17047555, 4096, [], 314543686139381359119154492, 314543686139381365083965499⟩
def PrimData22.s6 : Seg := ⟨314543686139381359119154492, 314543686139381365083965499, 17055747, 4096, [], 314701269189746607917160582, 314701269189746613884964493⟩
def PrimData22.s7 : Seg := ⟨314701269189746607917160582, 314701269189746613884964493, 17063939, 4096, [], 314858549656920155949071260, 314858549656920161919862243⟩
def PrimData22.s8 : Seg := ⟨314858549656920155949071260, 314858549656920161919862243, 17072131, 4096, [], 315009690715467799867760016, 315009690715467805841421431⟩
def PrimData22.s9 : Seg := ⟨315009690715467799867760016, 315009690715467805841421431, 17080323, 4096, [], 315155306390166262037704774, 315155306390166268014131645⟩
def PrimData22.s10 : Seg := ⟨315155306390166262037704774, 315155306390166268014131645, 17088515, 4096, [], 315312907602501472361805348, 315312907602501478341225123⟩
def PrimData22.s11 : Seg := ⟨315312907602501472361805348, 315312907602501478341225123, 17096707, 4096, [], 315461603857249789198048168, 315461603857249795180291719⟩
def PrimData22.s12 : Seg := ⟨315461603857249789198048168, 315461603857249795180291719, 17104899, 4096, [], 315610611665670262255433452, 315610611665670268240506611⟩
def PrimData22.s13 : Seg := ⟨315610611665670262255433452, 315610611665670268240506611, 17113091, 4096, [], 315762081659982103338270773, 315762081659982109326220196⟩
def PrimData22.s14 : Seg := ⟨315762081659982103338270773, 315762081659982109326220196, 17121283, 4096, [], 315913556043566308688180196, 315913556043566314679005883⟩
def PrimData22.s15 : Seg := ⟨315913556043566308688180196, 315913556043566314679005883, 17129475, 4096, [], 316064727523820470775906622, 316064727523820476769602741⟩
def PrimData22.s16 : Seg := ⟨316064727523820470775906622, 316064727523820476769602741, 17137667, 4096, [], 316212216179924672759989121, 316212216179924678756485688⟩
def PrimData22.s17 : Seg := ⟨316212216179924672759989121, 316212216179924678756485688, 17145859, 4096, [], 316360323581970235902798226, 316360323581970241902106905⟩
def PrimData22.s18 : Seg := ⟨316360323581970235902798226, 316360323581970241902106905, 17154051, 4096, [], 316510586204726767305603121, 316510586204726773307764736⟩
def PrimData22.s19 : Seg := ⟨316510586204726767305603121, 316510586204726773307764736, 17162243, 4096, [], 316655936461428844718167294, 316655936461428850723088533⟩
def PrimData22.s20 : Seg := ⟨316655936461428844718167294, 316655936461428850723088533, 17170435, 4096, [], 316801598123131250077070578, 316801598123131256084757273⟩
def PrimData22.s21 : Seg := ⟨316801598123131250077070578, 316801598123131256084757273, 17178627, 4096, [], 316950029773575651417761238, 316950029773575657428265877⟩
def PrimData22.s22 : Seg := ⟨316950029773575651417761238, 316950029773575657428265877, 17186819, 4096, [], 317100616950832522012628710, 317100616950832528025992117⟩
def PrimData22.s23 : Seg := ⟨317100616950832522012628710, 317100616950832528025992117, 17195011, 4096, [], 317248749813166529626705866, 317248749813166535642881385⟩
def PrimData22.s24 : Seg := ⟨317248749813166529626705866, 317248749813166535642881385, 17203203, 4096, [], 317398423556422742898621652, 317398423556422748917638443⟩
def PrimData22.s25 : Seg := ⟨317398423556422742898621652, 317398423556422748917638443, 17211395, 4096, [], 317546872257781051028188908, 317546872257781057050023643⟩
def PrimData22.s26 : Seg := ⟨317546872257781051028188908, 317546872257781057050023643, 17219587, 4096, [], 317697169230672549959522750, 317697169230672555984210421⟩
def PrimData22.s27 : Seg := ⟨317697169230672549959522750, 317697169230672555984210421, 17227779, 4096, [], 317857920935275175642861296, 317857920935275181670600191⟩
def PrimData22.s28 : Seg := ⟨317857920935275175642861296, 317857920935275181670600191, 17235971, 4096, [], 318009148638132891453002313, 318009148638132897483611640⟩
def PrimData22.s29 : Seg := ⟨318009148638132891453002313, 318009148638132897483611640, 17244163, 4096, [], 318154233010313745537527667, 318154233010313751570890786⟩
def PrimData22.s30 : Seg := ⟨318154233010313745537527667, 318154233010313751570890786, 17252355, 4096, [], 318307313707972923569282639, 318307313707972929605551182⟩
def PrimData22.s31 : Seg := ⟨318307313707972923569282639, 318307313707972929605551182, 17260547, 4096, [], 318454558130997212123744401, 318454558130997218162807560⟩
def PrimData22.s32 : Seg := ⟨318454558130997212123744401, 318454558130997218162807560, 17268739, 4096, [], 318606725300384161688090161, 318606725300384167730041248⟩
def PrimData22.s33 : Seg := ⟨318606725300384161688090161, 318606725300384167730041248, 17276931, 4096, [], 318759819046286606445303236, 318759819046286612490159747⟩
def PrimData22.s34 : Seg := ⟨318759819046286606445303236, 318759819046286612490159747, 17285123, 4096, [], 318914454335844904954429457, 318914454335844911002220552⟩

def PrimData22.segs : List Seg := [PrimData22.s0, PrimData22.s1, PrimData22.s2, PrimData22.s3, PrimData22.s4, PrimData22.s5, PrimData22.s6, PrimData22.s7, PrimData22.s8, PrimData22.s9, PrimData22.s10, PrimData22.s11, PrimData22.s12, PrimData22.s13, PrimData22.s14, PrimData22.s15, PrimData22.s16, PrimData22.s17, PrimData22.s18, PrimData22.s19, PrimData22.s20, PrimData22.s21, PrimData22.s22, PrimData22.s23, PrimData22.s24, PrimData22.s25, PrimData22.s26, PrimData22.s27, PrimData22.s28, PrimData22.s29, PrimData22.s30, PrimData22.s31, PrimData22.s32, PrimData22.s33, PrimData22.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked22_s0 : Seg.bok PrimData22.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s0

theorem checked22_s1 : Seg.bok PrimData22.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s1

theorem checked22_s2 : Seg.bok PrimData22.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s2

theorem checked22_s3 : Seg.bok PrimData22.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s3

theorem checked22_s4 : Seg.bok PrimData22.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s4

theorem checked22_s5 : Seg.bok PrimData22.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s5

theorem checked22_s6 : Seg.bok PrimData22.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s6

theorem checked22_s7 : Seg.bok PrimData22.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s7

theorem checked22_s8 : Seg.bok PrimData22.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s8

theorem checked22_s9 : Seg.bok PrimData22.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s9

theorem checked22_s10 : Seg.bok PrimData22.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s10

theorem checked22_s11 : Seg.bok PrimData22.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s11

theorem checked22_s12 : Seg.bok PrimData22.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s12

theorem checked22_s13 : Seg.bok PrimData22.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s13

theorem checked22_s14 : Seg.bok PrimData22.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s14

theorem checked22_s15 : Seg.bok PrimData22.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s15

theorem checked22_s16 : Seg.bok PrimData22.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s16

theorem checked22_s17 : Seg.bok PrimData22.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s17

theorem checked22_s18 : Seg.bok PrimData22.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s18

theorem checked22_s19 : Seg.bok PrimData22.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s19

theorem checked22_s20 : Seg.bok PrimData22.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s20

theorem checked22_s21 : Seg.bok PrimData22.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s21

theorem checked22_s22 : Seg.bok PrimData22.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s22

theorem checked22_s23 : Seg.bok PrimData22.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s23

theorem checked22_s24 : Seg.bok PrimData22.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s24

theorem checked22_s25 : Seg.bok PrimData22.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s25

theorem checked22_s26 : Seg.bok PrimData22.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s26

theorem checked22_s27 : Seg.bok PrimData22.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s27

theorem checked22_s28 : Seg.bok PrimData22.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s28

theorem checked22_s29 : Seg.bok PrimData22.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s29

theorem checked22_s30 : Seg.bok PrimData22.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s30

theorem checked22_s31 : Seg.bok PrimData22.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s31

theorem checked22_s32 : Seg.bok PrimData22.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s32

theorem checked22_s33 : Seg.bok PrimData22.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s33

theorem checked22_s34 : Seg.bok PrimData22.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22_s34

 theorem checked22 : ∀ s ∈ PrimData22.segs, (Seg.bok s) = true := by
  unfold PrimData22.segs
  exact List.forall_mem_cons.2 ⟨checked22_s0, List.forall_mem_cons.2 ⟨checked22_s1, List.forall_mem_cons.2 ⟨checked22_s2, List.forall_mem_cons.2 ⟨checked22_s3, List.forall_mem_cons.2 ⟨checked22_s4, List.forall_mem_cons.2 ⟨checked22_s5, List.forall_mem_cons.2 ⟨checked22_s6, List.forall_mem_cons.2 ⟨checked22_s7, List.forall_mem_cons.2 ⟨checked22_s8, List.forall_mem_cons.2 ⟨checked22_s9, List.forall_mem_cons.2 ⟨checked22_s10, List.forall_mem_cons.2 ⟨checked22_s11, List.forall_mem_cons.2 ⟨checked22_s12, List.forall_mem_cons.2 ⟨checked22_s13, List.forall_mem_cons.2 ⟨checked22_s14, List.forall_mem_cons.2 ⟨checked22_s15, List.forall_mem_cons.2 ⟨checked22_s16, List.forall_mem_cons.2 ⟨checked22_s17, List.forall_mem_cons.2 ⟨checked22_s18, List.forall_mem_cons.2 ⟨checked22_s19, List.forall_mem_cons.2 ⟨checked22_s20, List.forall_mem_cons.2 ⟨checked22_s21, List.forall_mem_cons.2 ⟨checked22_s22, List.forall_mem_cons.2 ⟨checked22_s23, List.forall_mem_cons.2 ⟨checked22_s24, List.forall_mem_cons.2 ⟨checked22_s25, List.forall_mem_cons.2 ⟨checked22_s26, List.forall_mem_cons.2 ⟨checked22_s27, List.forall_mem_cons.2 ⟨checked22_s28, List.forall_mem_cons.2 ⟨checked22_s29, List.forall_mem_cons.2 ⟨checked22_s30, List.forall_mem_cons.2 ⟨checked22_s31, List.forall_mem_cons.2 ⟨checked22_s32, List.forall_mem_cons.2 ⟨checked22_s33, List.forall_mem_singleton.2 checked22_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked22
