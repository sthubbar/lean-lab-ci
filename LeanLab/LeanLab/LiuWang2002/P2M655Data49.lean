/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_49.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/e7a4d85e-1143-43c6-8438-7441b6a94f8c
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData49.s0 : Seg := ⟨456440368808865448598245922, 456440368808865457253916777, 24748035, 4096, [], 456593936907758854180284122, 456593936907758862838866295⟩
def PrimData49.s1 : Seg := ⟨456593936907758854180284122, 456593936907758862838866295, 24756227, 4096, [], 456736830235313139714863534, 456736830235313148376154980⟩
def PrimData49.s2 : Seg := ⟨456736830235313139714863534, 456736830235313148376154980, 24764419, 4096, [], 456898569783740406555555421, 456898569783740415219914884⟩
def PrimData49.s3 : Seg := ⟨456898569783740406555555421, 456898569783740415219914884, 24772611, 4096, [], 457054031172220427327634184, 457054031172220435994941024⟩
def PrimData49.s4 : Seg := ⟨457054031172220427327634184, 457054031172220435994941024, 24780803, 4096, [], 457199759420396603021736283, 457199759420396611691805709⟩
def PrimData49.s5 : Seg := ⟨457199759420396603021736283, 457199759420396611691805709, 24788995, 4096, [], 457350515673836665268093420, 457350515673836673941021009⟩
def PrimData49.s6 : Seg := ⟨457350515673836665268093420, 457350515673836673941021009, 24797187, 4096, [], 457493108779048694366069182, 457493108779048703041700079⟩
def PrimData49.s7 : Seg := ⟨457493108779048694366069182, 457493108779048703041700079, 24805379, 4096, [], 457654549952284431142761657, 457654549952284439821453684⟩
def PrimData49.s8 : Seg := ⟨457654549952284431142761657, 457654549952284439821453684, 24813571, 4096, [], 457798404972066262808669691, 457798404972066271490088107⟩
def PrimData49.s9 : Seg := ⟨457798404972066262808669691, 457798404972066271490088107, 24821763, 4096, [], 457945717902186574328521449, 457945717902186583012732808⟩
def PrimData49.s10 : Seg := ⟨457945717902186574328521449, 457945717902186583012732808, 24829955, 4096, [], 458092405492129420725172784, 458092405492129429412166018⟩
def PrimData49.s11 : Seg := ⟨458092405492129420725172784, 458092405492129429412166018, 24838147, 4096, [], 458241608775057769850877338, 458241608775057778540699159⟩
def PrimData49.s12 : Seg := ⟨458241608775057769850877338, 458241608775057778540699159, 24846339, 4096, [], 458391443212869510070974606, 458391443212869518763637400⟩
def PrimData49.s13 : Seg := ⟨458391443212869510070974606, 458391443212869518763637400, 24854531, 4096, [], 458548505333077976285372430, 458548505333077984981013537⟩
def PrimData49.s14 : Seg := ⟨458548505333077976285372430, 458548505333077984981013537, 24862723, 4096, [], 458699602065887235524007089, 458699602065887244222513471⟩
def PrimData49.s15 : Seg := ⟨458699602065887235524007089, 458699602065887244222513471, 24870915, 4096, [], 458857926846760052702076501, 458857926846760061403585496⟩
def PrimData49.s16 : Seg := ⟨458857926846760052702076501, 458857926846760061403585496, 24879107, 4096, [], 459001804198550815954819192, 459001804198550824659057082⟩
def PrimData49.s17 : Seg := ⟨459001804198550815954819192, 459001804198550824659057082, 24887299, 4096, [], 459151338929341242996037247, 459151338929341251703111171⟩
def PrimData49.s18 : Seg := ⟨459151338929341242996037247, 459151338929341251703111171, 24895491, 4096, [], 459303075633927670504443869, 459303075633927679214395463⟩
def PrimData49.s19 : Seg := ⟨459303075633927670504443869, 459303075633927679214395463, 24903683, 4096, [], 459457642771934583021091419, 459457642771934591733974311⟩
def PrimData49.s20 : Seg := ⟨459457642771934583021091419, 459457642771934591733974311, 24911875, 4096, [], 459593991157049136707457286, 459593991157049145422925929⟩
def PrimData49.s21 : Seg := ⟨459593991157049136707457286, 459593991157049145422925929, 24920067, 4096, [], 459748250026854846583438626, 459748250026854855301833293⟩
def PrimData49.s22 : Seg := ⟨459748250026854846583438626, 459748250026854855301833293, 24928259, 4096, [], 459896856680086571301612486, 459896856680086580022825551⟩
def PrimData49.s23 : Seg := ⟨459896856680086571301612486, 459896856680086580022825551, 24936451, 4096, [], 460046722953723367952775329, 460046722953723376676831863⟩
def PrimData49.s24 : Seg := ⟨460046722953723367952775329, 460046722953723376676831863, 24944643, 4096, [], 460194392765689701582627672, 460194392765689710309485884⟩
def PrimData49.s25 : Seg := ⟨460194392765689701582627672, 460194392765689710309485884, 24952835, 4096, [], 460351805532089736117079988, 460351805532089744846924566⟩
def PrimData49.s26 : Seg := ⟨460351805532089736117079988, 460351805532089744846924566, 24961027, 4096, [], 460504822498946752458214258, 460504822498946761190961601⟩
def PrimData49.s27 : Seg := ⟨460504822498946752458214258, 460504822498946761190961601, 24969219, 4096, [], 460663498187985252067671983, 460663498187985260803429986⟩
def PrimData49.s28 : Seg := ⟨460663498187985252067671983, 460663498187985260803429986, 24977411, 4096, [], 460812122011689939446594057, 460812122011689948185171016⟩
def PrimData49.s29 : Seg := ⟨460812122011689939446594057, 460812122011689948185171016, 24985603, 4096, [], 460962634076412467299589481, 460962634076412476041020876⟩
def PrimData49.s30 : Seg := ⟨460962634076412467299589481, 460962634076412476041020876, 24993795, 4096, [], 461111892146643164927024744, 461111892146643173671286750⟩
def PrimData49.s31 : Seg := ⟨461111892146643164927024744, 461111892146643173671286750, 25001987, 4096, [], 461264295361880051027352022, 461264295361880059774504675⟩
def PrimData49.s32 : Seg := ⟨461264295361880051027352022, 461264295361880059774504675, 25010179, 4096, [], 461420472354249940225125349, 461420472354249948975241048⟩
def PrimData49.s33 : Seg := ⟨461420472354249940225125349, 461420472354249948975241048, 25018371, 4096, [], 461569424733594825774410369, 461569424733594834527350853⟩
def PrimData49.s34 : Seg := ⟨461569424733594825774410369, 461569424733594834527350853, 25026563, 4096, [], 461713351952353214297259272, 461713351952353223052929298⟩

def PrimData49.segs : List Seg := [PrimData49.s0, PrimData49.s1, PrimData49.s2, PrimData49.s3, PrimData49.s4, PrimData49.s5, PrimData49.s6, PrimData49.s7, PrimData49.s8, PrimData49.s9, PrimData49.s10, PrimData49.s11, PrimData49.s12, PrimData49.s13, PrimData49.s14, PrimData49.s15, PrimData49.s16, PrimData49.s17, PrimData49.s18, PrimData49.s19, PrimData49.s20, PrimData49.s21, PrimData49.s22, PrimData49.s23, PrimData49.s24, PrimData49.s25, PrimData49.s26, PrimData49.s27, PrimData49.s28, PrimData49.s29, PrimData49.s30, PrimData49.s31, PrimData49.s32, PrimData49.s33, PrimData49.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked49_s0 : Seg.bok PrimData49.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s0

theorem checked49_s1 : Seg.bok PrimData49.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s1

theorem checked49_s2 : Seg.bok PrimData49.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s2

theorem checked49_s3 : Seg.bok PrimData49.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s3

theorem checked49_s4 : Seg.bok PrimData49.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s4

theorem checked49_s5 : Seg.bok PrimData49.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s5

theorem checked49_s6 : Seg.bok PrimData49.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s6

theorem checked49_s7 : Seg.bok PrimData49.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s7

theorem checked49_s8 : Seg.bok PrimData49.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s8

theorem checked49_s9 : Seg.bok PrimData49.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s9

theorem checked49_s10 : Seg.bok PrimData49.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s10

theorem checked49_s11 : Seg.bok PrimData49.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s11

theorem checked49_s12 : Seg.bok PrimData49.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s12

theorem checked49_s13 : Seg.bok PrimData49.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s13

theorem checked49_s14 : Seg.bok PrimData49.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s14

theorem checked49_s15 : Seg.bok PrimData49.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s15

theorem checked49_s16 : Seg.bok PrimData49.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s16

theorem checked49_s17 : Seg.bok PrimData49.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s17

theorem checked49_s18 : Seg.bok PrimData49.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s18

theorem checked49_s19 : Seg.bok PrimData49.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s19

theorem checked49_s20 : Seg.bok PrimData49.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s20

theorem checked49_s21 : Seg.bok PrimData49.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s21

theorem checked49_s22 : Seg.bok PrimData49.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s22

theorem checked49_s23 : Seg.bok PrimData49.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s23

theorem checked49_s24 : Seg.bok PrimData49.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s24

theorem checked49_s25 : Seg.bok PrimData49.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s25

theorem checked49_s26 : Seg.bok PrimData49.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s26

theorem checked49_s27 : Seg.bok PrimData49.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s27

theorem checked49_s28 : Seg.bok PrimData49.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s28

theorem checked49_s29 : Seg.bok PrimData49.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s29

theorem checked49_s30 : Seg.bok PrimData49.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s30

theorem checked49_s31 : Seg.bok PrimData49.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s31

theorem checked49_s32 : Seg.bok PrimData49.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s32

theorem checked49_s33 : Seg.bok PrimData49.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s33

theorem checked49_s34 : Seg.bok PrimData49.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49_s34

 theorem checked49 : ∀ s ∈ PrimData49.segs, (Seg.bok s) = true := by
  unfold PrimData49.segs
  exact List.forall_mem_cons.2 ⟨checked49_s0, List.forall_mem_cons.2 ⟨checked49_s1, List.forall_mem_cons.2 ⟨checked49_s2, List.forall_mem_cons.2 ⟨checked49_s3, List.forall_mem_cons.2 ⟨checked49_s4, List.forall_mem_cons.2 ⟨checked49_s5, List.forall_mem_cons.2 ⟨checked49_s6, List.forall_mem_cons.2 ⟨checked49_s7, List.forall_mem_cons.2 ⟨checked49_s8, List.forall_mem_cons.2 ⟨checked49_s9, List.forall_mem_cons.2 ⟨checked49_s10, List.forall_mem_cons.2 ⟨checked49_s11, List.forall_mem_cons.2 ⟨checked49_s12, List.forall_mem_cons.2 ⟨checked49_s13, List.forall_mem_cons.2 ⟨checked49_s14, List.forall_mem_cons.2 ⟨checked49_s15, List.forall_mem_cons.2 ⟨checked49_s16, List.forall_mem_cons.2 ⟨checked49_s17, List.forall_mem_cons.2 ⟨checked49_s18, List.forall_mem_cons.2 ⟨checked49_s19, List.forall_mem_cons.2 ⟨checked49_s20, List.forall_mem_cons.2 ⟨checked49_s21, List.forall_mem_cons.2 ⟨checked49_s22, List.forall_mem_cons.2 ⟨checked49_s23, List.forall_mem_cons.2 ⟨checked49_s24, List.forall_mem_cons.2 ⟨checked49_s25, List.forall_mem_cons.2 ⟨checked49_s26, List.forall_mem_cons.2 ⟨checked49_s27, List.forall_mem_cons.2 ⟨checked49_s28, List.forall_mem_cons.2 ⟨checked49_s29, List.forall_mem_cons.2 ⟨checked49_s30, List.forall_mem_cons.2 ⟨checked49_s31, List.forall_mem_cons.2 ⟨checked49_s32, List.forall_mem_cons.2 ⟨checked49_s33, List.forall_mem_singleton.2 checked49_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked49
