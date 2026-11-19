/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_73.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/313baab7-5410-41a2-94e7-4829da2621bd
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData73.s0 : Seg := ⟨583358663318200826020659948, 583358663318200837083254480, 31629315, 4096, [], 583509347001600585839156008, 583509347001600596904609306⟩
def PrimData73.s1 : Seg := ⟨583509347001600585839156008, 583509347001600596904609306, 31637507, 4096, [], 583660032992738699372911656, 583660032992738710441223853⟩
def PrimData73.s2 : Seg := ⟨583660032992738699372911656, 583660032992738710441223853, 31645699, 4096, [], 583809765472296022165609390, 583809765472296033236762185⟩
def PrimData73.s3 : Seg := ⟨583809765472296022165609390, 583809765472296033236762185, 31653891, 4096, [], 583961411703552883521661946, 583961411703552894595691689⟩
def PrimData73.s4 : Seg := ⟨583961411703552883521661946, 583961411703552894595691689, 31662083, 4096, [], 584108918555416428587143569, 584108918555416439663971528⟩
def PrimData73.s5 : Seg := ⟨584108918555416428587143569, 584108918555416439663971528, 31670275, 4096, [], 584272038691291493934008894, 584272038691291505013932561⟩
def PrimData73.s6 : Seg := ⟨584272038691291493934008894, 584272038691291505013932561, 31678467, 4096, [], 584417638331726326620553341, 584417638331726337703238348⟩
def PrimData73.s7 : Seg := ⟨584417638331726326620553341, 584417638331726337703238348, 31686659, 4096, [], 584572479691803068184482022, 584572479691803079270104091⟩
def PrimData73.s8 : Seg := ⟨584572479691803068184482022, 584572479691803079270104091, 31694851, 4096, [], 584728916409354837004046512, 584728916409354848092636725⟩
def PrimData73.s9 : Seg := ⟨584728916409354837004046512, 584728916409354848092636725, 31703043, 4096, [], 584874841248951181209019363, 584874841248951192300377462⟩
def PrimData73.s10 : Seg := ⟨584874841248951181209019363, 584874841248951192300377462, 31711235, 4096, [], 585018856538790874944669640, 585018856538790886038759175⟩
def PrimData73.s11 : Seg := ⟨585018856538790874944669640, 585018856538790886038759175, 31719427, 4096, [], 585166060233860518093846474, 585166060233860529190728195⟩
def PrimData73.s12 : Seg := ⟨585166060233860518093846474, 585166060233860529190728195, 31727619, 4096, [], 585315815089202888915527751, 585315815089202900015250064⟩
def PrimData73.s13 : Seg := ⟨585315815089202888915527751, 585315815089202900015250064, 31735811, 4096, [], 585470351699791164362964219, 585470351699791175465618203⟩
def PrimData73.s14 : Seg := ⟨585470351699791164362964219, 585470351699791175465618203, 31744003, 4096, [], 585620429690838822014700921, 585620429690838833120201766⟩
def PrimData73.s15 : Seg := ⟨585620429690838822014700921, 585620429690838833120201766, 31752195, 4096, [], 585763499814176824286085581, 585763499814176835394299655⟩
def PrimData73.s16 : Seg := ⟨585763499814176824286085581, 585763499814176835394299655, 31760387, 4096, [], 585918999301107943106930307, 585918999301107954218094219⟩
def PrimData73.s17 : Seg := ⟨585918999301107943106930307, 585918999301107954218094219, 31768579, 4096, [], 586072589183855793527582099, 586072589183855804641659559⟩
def PrimData73.s18 : Seg := ⟨586072589183855793527582099, 586072589183855804641659559, 31776771, 4096, [], 586225225388845076119284559, 586225225388845087236257480⟩
def PrimData73.s19 : Seg := ⟨586225225388845076119284559, 586225225388845087236257480, 31784963, 4096, [], 586374039925320885190635822, 586374039925320896310431304⟩
def PrimData73.s20 : Seg := ⟨586374039925320885190635822, 586374039925320896310431304, 31793155, 4096, [], 586522538073996627078621066, 586522538073996638201232804⟩
def PrimData73.s21 : Seg := ⟨586522538073996627078621066, 586522538073996638201232804, 31801347, 4096, [], 586678686493596820592411646, 586678686493596831717985444⟩
def PrimData73.s22 : Seg := ⟨586678686493596820592411646, 586678686493596831717985444, 31809539, 4096, [], 586833243859368459855350005, 586833243859368470983855688⟩
def PrimData73.s23 : Seg := ⟨586833243859368459855350005, 586833243859368470983855688, 31817731, 4096, [], 586984298060911798971300347, 586984298060911810102670875⟩
def PrimData73.s24 : Seg := ⟨586984298060911798971300347, 586984298060911810102670875, 31825923, 4096, [], 587136310578827576792904751, 587136310578827587927158374⟩
def PrimData73.s25 : Seg := ⟨587136310578827576792904751, 587136310578827587927158374, 31834115, 4096, [], 587288962733284031592708705, 587288962733284042729857581⟩
def PrimData73.s26 : Seg := ⟨587288962733284031592708705, 587288962733284042729857581, 31842307, 4096, [], 587438430181135987791271221, 587438430181135998931254605⟩
def PrimData73.s27 : Seg := ⟨587438430181135987791271221, 587438430181135998931254605, 31850499, 4096, [], 587598416898883037558315465, 587598416898883048701334035⟩
def PrimData73.s28 : Seg := ⟨587598416898883037558315465, 587598416898883048701334035, 31858691, 4096, [], 587750438439904290156014394, 587750438439904301301916276⟩
def PrimData73.s29 : Seg := ⟨587750438439904290156014394, 587750438439904301301916276, 31866883, 4096, [], 587898956454633897375871743, 587898956454633908524590112⟩
def PrimData73.s30 : Seg := ⟨587898956454633897375871743, 587898956454633908524590112, 31875075, 4096, [], 588056081904726752389906375, 588056081904726763541605083⟩
def PrimData73.s31 : Seg := ⟨588056081904726752389906375, 588056081904726763541605083, 31883267, 4096, [], 588200142282709424147159580, 588200142282709435301589724⟩
def PrimData73.s32 : Seg := ⟨588200142282709424147159580, 588200142282709435301589724, 31891459, 4096, [], 588351216739452053000042222, 588351216739452064157337322⟩
def PrimData73.s33 : Seg := ⟨588351216739452053000042222, 588351216739452064157337322, 31899651, 4096, [], 588501018537097502418371561, 588501018537097513578507338⟩
def PrimData73.s34 : Seg := ⟨588501018537097502418371561, 588501018537097513578507338, 31907843, 4096, [], 588650822501545982291308738, 588650822501545993454285301⟩

def PrimData73.segs : List Seg := [PrimData73.s0, PrimData73.s1, PrimData73.s2, PrimData73.s3, PrimData73.s4, PrimData73.s5, PrimData73.s6, PrimData73.s7, PrimData73.s8, PrimData73.s9, PrimData73.s10, PrimData73.s11, PrimData73.s12, PrimData73.s13, PrimData73.s14, PrimData73.s15, PrimData73.s16, PrimData73.s17, PrimData73.s18, PrimData73.s19, PrimData73.s20, PrimData73.s21, PrimData73.s22, PrimData73.s23, PrimData73.s24, PrimData73.s25, PrimData73.s26, PrimData73.s27, PrimData73.s28, PrimData73.s29, PrimData73.s30, PrimData73.s31, PrimData73.s32, PrimData73.s33, PrimData73.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked73_s0 : Seg.bok PrimData73.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s0

theorem checked73_s1 : Seg.bok PrimData73.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s1

theorem checked73_s2 : Seg.bok PrimData73.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s2

theorem checked73_s3 : Seg.bok PrimData73.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s3

theorem checked73_s4 : Seg.bok PrimData73.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s4

theorem checked73_s5 : Seg.bok PrimData73.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s5

theorem checked73_s6 : Seg.bok PrimData73.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s6

theorem checked73_s7 : Seg.bok PrimData73.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s7

theorem checked73_s8 : Seg.bok PrimData73.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s8

theorem checked73_s9 : Seg.bok PrimData73.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s9

theorem checked73_s10 : Seg.bok PrimData73.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s10

theorem checked73_s11 : Seg.bok PrimData73.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s11

theorem checked73_s12 : Seg.bok PrimData73.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s12

theorem checked73_s13 : Seg.bok PrimData73.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s13

theorem checked73_s14 : Seg.bok PrimData73.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s14

theorem checked73_s15 : Seg.bok PrimData73.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s15

theorem checked73_s16 : Seg.bok PrimData73.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s16

theorem checked73_s17 : Seg.bok PrimData73.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s17

theorem checked73_s18 : Seg.bok PrimData73.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s18

theorem checked73_s19 : Seg.bok PrimData73.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s19

theorem checked73_s20 : Seg.bok PrimData73.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s20

theorem checked73_s21 : Seg.bok PrimData73.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s21

theorem checked73_s22 : Seg.bok PrimData73.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s22

theorem checked73_s23 : Seg.bok PrimData73.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s23

theorem checked73_s24 : Seg.bok PrimData73.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s24

theorem checked73_s25 : Seg.bok PrimData73.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s25

theorem checked73_s26 : Seg.bok PrimData73.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s26

theorem checked73_s27 : Seg.bok PrimData73.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s27

theorem checked73_s28 : Seg.bok PrimData73.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s28

theorem checked73_s29 : Seg.bok PrimData73.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s29

theorem checked73_s30 : Seg.bok PrimData73.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s30

theorem checked73_s31 : Seg.bok PrimData73.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s31

theorem checked73_s32 : Seg.bok PrimData73.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s32

theorem checked73_s33 : Seg.bok PrimData73.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s33

theorem checked73_s34 : Seg.bok PrimData73.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73_s34

 theorem checked73 : ∀ s ∈ PrimData73.segs, (Seg.bok s) = true := by
  unfold PrimData73.segs
  exact List.forall_mem_cons.2 ⟨checked73_s0, List.forall_mem_cons.2 ⟨checked73_s1, List.forall_mem_cons.2 ⟨checked73_s2, List.forall_mem_cons.2 ⟨checked73_s3, List.forall_mem_cons.2 ⟨checked73_s4, List.forall_mem_cons.2 ⟨checked73_s5, List.forall_mem_cons.2 ⟨checked73_s6, List.forall_mem_cons.2 ⟨checked73_s7, List.forall_mem_cons.2 ⟨checked73_s8, List.forall_mem_cons.2 ⟨checked73_s9, List.forall_mem_cons.2 ⟨checked73_s10, List.forall_mem_cons.2 ⟨checked73_s11, List.forall_mem_cons.2 ⟨checked73_s12, List.forall_mem_cons.2 ⟨checked73_s13, List.forall_mem_cons.2 ⟨checked73_s14, List.forall_mem_cons.2 ⟨checked73_s15, List.forall_mem_cons.2 ⟨checked73_s16, List.forall_mem_cons.2 ⟨checked73_s17, List.forall_mem_cons.2 ⟨checked73_s18, List.forall_mem_cons.2 ⟨checked73_s19, List.forall_mem_cons.2 ⟨checked73_s20, List.forall_mem_cons.2 ⟨checked73_s21, List.forall_mem_cons.2 ⟨checked73_s22, List.forall_mem_cons.2 ⟨checked73_s23, List.forall_mem_cons.2 ⟨checked73_s24, List.forall_mem_cons.2 ⟨checked73_s25, List.forall_mem_cons.2 ⟨checked73_s26, List.forall_mem_cons.2 ⟨checked73_s27, List.forall_mem_cons.2 ⟨checked73_s28, List.forall_mem_cons.2 ⟨checked73_s29, List.forall_mem_cons.2 ⟨checked73_s30, List.forall_mem_cons.2 ⟨checked73_s31, List.forall_mem_cons.2 ⟨checked73_s32, List.forall_mem_cons.2 ⟨checked73_s33, List.forall_mem_singleton.2 checked73_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked73
