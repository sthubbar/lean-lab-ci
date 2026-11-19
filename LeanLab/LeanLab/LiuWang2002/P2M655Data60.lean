/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_60.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/a9872b3b-28fc-493d-bb05-876894ab0846
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData60.s0 : Seg := ⟨514592991377577003739254072, 514592991377577013497693776, 27901955, 4096, [], 514747641304412948524654698, 514747641304412958286027116⟩
def PrimData60.s1 : Seg := ⟨514747641304412948524654698, 514747641304412958286027116, 27910147, 4096, [], 514901028835377943108261989, 514901028835377952872543304⟩
def PrimData60.s2 : Seg := ⟨514901028835377943108261989, 514901028835377952872543304, 27918339, 4096, [], 515054102693145737433380666, 515054102693145747200564833⟩
def PrimData60.s3 : Seg := ⟨515054102693145737433380666, 515054102693145747200564833, 27926531, 4096, [], 515208760583738041033690017, 515208760583738050803805527⟩
def PrimData60.s4 : Seg := ⟨515208760583738041033690017, 515208760583738050803805527, 27934723, 4096, [], 515354565299973927689022675, 515354565299973937461901284⟩
def PrimData60.s5 : Seg := ⟨515354565299973927689022675, 515354565299973937461901284, 27942915, 4096, [], 515505116723443840712100853, 515505116723443850487833559⟩
def PrimData60.s6 : Seg := ⟨515505116723443840712100853, 515505116723443850487833559, 27951107, 4096, [], 515659466251864790525373282, 515659466251864800304033466⟩
def PrimData60.s7 : Seg := ⟨515659466251864790525373282, 515659466251864800304033466, 27959299, 4096, [], 515814767334603385151177315, 515814767334603394932781506⟩
def PrimData60.s8 : Seg := ⟨515814767334603385151177315, 515814767334603394932781506, 27967491, 4096, [], 515966591724683918304026113, 515966591724683928088507892⟩
def PrimData60.s9 : Seg := ⟨515966591724683918304026113, 515966591724683928088507892, 27975683, 4096, [], 516113674093098546708232845, 516113674093098556495503412⟩
def PrimData60.s10 : Seg := ⟨516113674093098546708232845, 516113674093098556495503412, 27983875, 4096, [], 516262024227847813838015355, 516262024227847823628098437⟩
def PrimData60.s11 : Seg := ⟨516262024227847813838015355, 516262024227847823628098437, 27992067, 4096, [], 516409111607678963999078501, 516409111607678973791949586⟩
def PrimData60.s12 : Seg := ⟨516409111607678963999078501, 516409111607678973791949586, 28000259, 4096, [], 516560630023967160194823746, 516560630023967169990567413⟩
def PrimData60.s13 : Seg := ⟨516560630023967160194823746, 516560630023967169990567413, 28008451, 4096, [], 516718161255681100057273553, 516718161255681109856003575⟩
def PrimData60.s14 : Seg := ⟨516718161255681100057273553, 516718161255681109856003575, 28016643, 4096, [], 516874429862769861219047695, 516874429862769871020740541⟩
def PrimData60.s15 : Seg := ⟨516874429862769861219047695, 516874429862769871020740541, 28024835, 4096, [], 517025323315084829998499498, 517025323315084839803053015⟩
def PrimData60.s16 : Seg := ⟨517025323315084829998499498, 517025323315084839803053015, 28033027, 4096, [], 517183178901199270991863471, 517183178901199280799409659⟩
def PrimData60.s17 : Seg := ⟨517183178901199270991863471, 517183178901199280799409659, 28041219, 4096, [], 517333128553488155428266465, 517333128553488165238654408⟩
def PrimData60.s18 : Seg := ⟨517333128553488155428266465, 517333128553488165238654408, 28049411, 4096, [], 517466946593678990696854450, 517466946593679000509778244⟩
def PrimData60.s19 : Seg := ⟨517466946593678990696854450, 517466946593679000509778244, 28057603, 4096, [], 517617850345194235251629014, 517617850345194245067413472⟩
def PrimData60.s20 : Seg := ⟨517617850345194235251629014, 517617850345194245067413472, 28065795, 4096, [], 517771920350448474226827623, 517771920350448484045533149⟩
def PrimData60.s21 : Seg := ⟨517771920350448474226827623, 517771920350448484045533149, 28073987, 4096, [], 517924727505648037365482925, 517924727505648047187085277⟩
def PrimData60.s22 : Seg := ⟨517924727505648037365482925, 517924727505648047187085277, 28082179, 4096, [], 518078486353929331665975704, 518078486353929341490493128⟩
def PrimData60.s23 : Seg := ⟨518078486353929331665975704, 518078486353929341490493128, 28090371, 4096, [], 518232880631833294429671769, 518232880631833304257116911⟩
def PrimData60.s24 : Seg := ⟨518232880631833294429671769, 518232880631833304257116911, 28098563, 4096, [], 518378418631922789392287967, 518378418631922799222492017⟩
def PrimData60.s25 : Seg := ⟨518378418631922789392287967, 518378418631922799222492017, 28106755, 4096, [], 518526806671976656528481115, 518526806671976666361498053⟩
def PrimData60.s26 : Seg := ⟨518526806671976656528481115, 518526806671976666361498053, 28114947, 4096, [], 518674564426352152571908810, 518674564426352162407726638⟩
def PrimData60.s27 : Seg := ⟨518674564426352152571908810, 518674564426352162407726638, 28123139, 4096, [], 518828969183675175858408516, 518828969183675185697154710⟩
def PrimData60.s28 : Seg := ⟨518828969183675175858408516, 518828969183675185697154710, 28131331, 4096, [], 518978630445360722168576304, 518978630445360732010159384⟩
def PrimData60.s29 : Seg := ⟨518978630445360722168576304, 518978630445360732010159384, 28139523, 4096, [], 519136837416484531344622350, 519136837416484541189204923⟩
def PrimData60.s30 : Seg := ⟨519136837416484531344622350, 519136837416484541189204923, 28147715, 4096, [], 519291250037015767911987968, 519291250037015777759498089⟩
def PrimData60.s31 : Seg := ⟨519291250037015767911987968, 519291250037015777759498089, 28155907, 4096, [], 519436488963209892676396059, 519436488963209902526660324⟩
def PrimData60.s32 : Seg := ⟨519436488963209892676396059, 519436488963209902526660324, 28164099, 4096, [], 519586160374961132069060818, 519586160374961141922163008⟩
def PrimData60.s33 : Seg := ⟨519586160374961132069060818, 519586160374961141922163008, 28172291, 4096, [], 519734884969125396542354844, 519734884969125406398277836⟩
def PrimData60.s34 : Seg := ⟨519734884969125396542354844, 519734884969125406398277836, 28180483, 4096, [], 519880131265099147414946211, 519880131265099157273623576⟩

def PrimData60.segs : List Seg := [PrimData60.s0, PrimData60.s1, PrimData60.s2, PrimData60.s3, PrimData60.s4, PrimData60.s5, PrimData60.s6, PrimData60.s7, PrimData60.s8, PrimData60.s9, PrimData60.s10, PrimData60.s11, PrimData60.s12, PrimData60.s13, PrimData60.s14, PrimData60.s15, PrimData60.s16, PrimData60.s17, PrimData60.s18, PrimData60.s19, PrimData60.s20, PrimData60.s21, PrimData60.s22, PrimData60.s23, PrimData60.s24, PrimData60.s25, PrimData60.s26, PrimData60.s27, PrimData60.s28, PrimData60.s29, PrimData60.s30, PrimData60.s31, PrimData60.s32, PrimData60.s33, PrimData60.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked60_s0 : Seg.bok PrimData60.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s0

theorem checked60_s1 : Seg.bok PrimData60.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s1

theorem checked60_s2 : Seg.bok PrimData60.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s2

theorem checked60_s3 : Seg.bok PrimData60.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s3

theorem checked60_s4 : Seg.bok PrimData60.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s4

theorem checked60_s5 : Seg.bok PrimData60.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s5

theorem checked60_s6 : Seg.bok PrimData60.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s6

theorem checked60_s7 : Seg.bok PrimData60.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s7

theorem checked60_s8 : Seg.bok PrimData60.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s8

theorem checked60_s9 : Seg.bok PrimData60.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s9

theorem checked60_s10 : Seg.bok PrimData60.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s10

theorem checked60_s11 : Seg.bok PrimData60.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s11

theorem checked60_s12 : Seg.bok PrimData60.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s12

theorem checked60_s13 : Seg.bok PrimData60.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s13

theorem checked60_s14 : Seg.bok PrimData60.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s14

theorem checked60_s15 : Seg.bok PrimData60.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s15

theorem checked60_s16 : Seg.bok PrimData60.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s16

theorem checked60_s17 : Seg.bok PrimData60.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s17

theorem checked60_s18 : Seg.bok PrimData60.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s18

theorem checked60_s19 : Seg.bok PrimData60.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s19

theorem checked60_s20 : Seg.bok PrimData60.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s20

theorem checked60_s21 : Seg.bok PrimData60.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s21

theorem checked60_s22 : Seg.bok PrimData60.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s22

theorem checked60_s23 : Seg.bok PrimData60.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s23

theorem checked60_s24 : Seg.bok PrimData60.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s24

theorem checked60_s25 : Seg.bok PrimData60.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s25

theorem checked60_s26 : Seg.bok PrimData60.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s26

theorem checked60_s27 : Seg.bok PrimData60.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s27

theorem checked60_s28 : Seg.bok PrimData60.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s28

theorem checked60_s29 : Seg.bok PrimData60.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s29

theorem checked60_s30 : Seg.bok PrimData60.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s30

theorem checked60_s31 : Seg.bok PrimData60.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s31

theorem checked60_s32 : Seg.bok PrimData60.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s32

theorem checked60_s33 : Seg.bok PrimData60.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s33

theorem checked60_s34 : Seg.bok PrimData60.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60_s34

 theorem checked60 : ∀ s ∈ PrimData60.segs, (Seg.bok s) = true := by
  unfold PrimData60.segs
  exact List.forall_mem_cons.2 ⟨checked60_s0, List.forall_mem_cons.2 ⟨checked60_s1, List.forall_mem_cons.2 ⟨checked60_s2, List.forall_mem_cons.2 ⟨checked60_s3, List.forall_mem_cons.2 ⟨checked60_s4, List.forall_mem_cons.2 ⟨checked60_s5, List.forall_mem_cons.2 ⟨checked60_s6, List.forall_mem_cons.2 ⟨checked60_s7, List.forall_mem_cons.2 ⟨checked60_s8, List.forall_mem_cons.2 ⟨checked60_s9, List.forall_mem_cons.2 ⟨checked60_s10, List.forall_mem_cons.2 ⟨checked60_s11, List.forall_mem_cons.2 ⟨checked60_s12, List.forall_mem_cons.2 ⟨checked60_s13, List.forall_mem_cons.2 ⟨checked60_s14, List.forall_mem_cons.2 ⟨checked60_s15, List.forall_mem_cons.2 ⟨checked60_s16, List.forall_mem_cons.2 ⟨checked60_s17, List.forall_mem_cons.2 ⟨checked60_s18, List.forall_mem_cons.2 ⟨checked60_s19, List.forall_mem_cons.2 ⟨checked60_s20, List.forall_mem_cons.2 ⟨checked60_s21, List.forall_mem_cons.2 ⟨checked60_s22, List.forall_mem_cons.2 ⟨checked60_s23, List.forall_mem_cons.2 ⟨checked60_s24, List.forall_mem_cons.2 ⟨checked60_s25, List.forall_mem_cons.2 ⟨checked60_s26, List.forall_mem_cons.2 ⟨checked60_s27, List.forall_mem_cons.2 ⟨checked60_s28, List.forall_mem_cons.2 ⟨checked60_s29, List.forall_mem_cons.2 ⟨checked60_s30, List.forall_mem_cons.2 ⟨checked60_s31, List.forall_mem_cons.2 ⟨checked60_s32, List.forall_mem_cons.2 ⟨checked60_s33, List.forall_mem_singleton.2 checked60_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked60
