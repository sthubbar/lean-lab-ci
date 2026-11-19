/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_50.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/ae1e9b58-3fbd-4758-ac09-639d0283a707
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData50.s0 : Seg := ⟨461713351952353214297259272, 461713351952353223052929298, 25034755, 4096, [], 461860424524401945484376284, 461860424524401954242835849⟩
def PrimData50.s1 : Seg := ⟨461860424524401945484376284, 461860424524401954242835849, 25042947, 4096, [], 462010328313015300461371604, 462010328313015309222675636⟩
def PrimData50.s2 : Seg := ⟨462010328313015300461371604, 462010328313015309222675636, 25051139, 4096, [], 462163377657512722621577254, 462163377657512731385782964⟩
def PrimData50.s3 : Seg := ⟨462163377657512722621577254, 462163377657512731385782964, 25059331, 4096, [], 462318629850137973511324641, 462318629850137982278474564⟩
def PrimData50.s4 : Seg := ⟨462318629850137973511324641, 462318629850137982278474564, 25067523, 4096, [], 462469485118595497286845854, 462469485118595506056856118⟩
def PrimData50.s5 : Seg := ⟨462469485118595497286845854, 462469485118595506056856118, 25075715, 4096, [], 462624428987121162101336679, 462624428987121170874285690⟩
def PrimData50.s6 : Seg := ⟨462624428987121162101336679, 462624428987121170874285690, 25083907, 4096, [], 462773089911942974811196357, 462773089911942983586964974⟩
def PrimData50.s7 : Seg := ⟨462773089911942974811196357, 462773089911942983586964974, 25092099, 4096, [], 462925839627147829956816352, 462925839627147838735481120⟩
def PrimData50.s8 : Seg := ⟨462925839627147829956816352, 462925839627147838735481120, 25100291, 4096, [], 463082363923144643339658581, 463082363923144652121291941⟩
def PrimData50.s9 : Seg := ⟨463082363923144643339658581, 463082363923144652121291941, 25108483, 4096, [], 463239519839835996391552704, 463239519839836005176167337⟩
def PrimData50.s10 : Seg := ⟨463239519839835996391552704, 463239519839836005176167337, 25116675, 4096, [], 463391335339365046131465827, 463391335339365054918959714⟩
def PrimData50.s11 : Seg := ⟨463391335339365046131465827, 463391335339365054918959714, 25124867, 4096, [], 463542839458433743060535090, 463542839458433751850902588⟩
def PrimData50.s12 : Seg := ⟨463542839458433743060535090, 463542839458433751850902588, 25133059, 4096, [], 463685545210574776137816492, 463685545210574784930889330⟩
def PrimData50.s13 : Seg := ⟨463685545210574776137816492, 463685545210574784930889330, 25141251, 4096, [], 463831397075713796041927181, 463831397075713804837765817⟩
def PrimData50.s14 : Seg := ⟨463831397075713796041927181, 463831397075713804837765817, 25149443, 4096, [], 463975365701909898382580923, 463975365701909907181148727⟩
def PrimData50.s15 : Seg := ⟨463975365701909898382580923, 463975365701909907181148727, 25157635, 4096, [], 464129081875481033368354695, 464129081875481042169838005⟩
def PrimData50.s16 : Seg := ⟨464129081875481033368354695, 464129081875481042169838005, 25165827, 4096, [], 464280286156291587410547198, 464280286156291596214898154⟩
def PrimData50.s17 : Seg := ⟨464280286156291587410547198, 464280286156291596214898154, 25174019, 4096, [], 464425520428282366102954221, 464425520428282374910059173⟩
def PrimData50.s18 : Seg := ⟨464425520428282366102954221, 464425520428282374910059173, 25182211, 4096, [], 464582389004732056395105510, 464582389004732065205184692⟩
def PrimData50.s19 : Seg := ⟨464582389004732056395105510, 464582389004732065205184692, 25190403, 4096, [], 464729200689581571188123601, 464729200689581580000987355⟩
def PrimData50.s20 : Seg := ⟨464729200689581571188123601, 464729200689581580000987355, 25198595, 4096, [], 464873185754137722733446174, 464873185754137731549038751⟩
def PrimData50.s21 : Seg := ⟨464873185754137722733446174, 464873185754137731549038751, 25206787, 4096, [], 465025976343475291467316861, 465025976343475300285806734⟩
def PrimData50.s22 : Seg := ⟨465025976343475291467316861, 465025976343475300285806734, 25214979, 4096, [], 465170595718079280468056708, 465170595718079289289288630⟩
def PrimData50.s23 : Seg := ⟨465170595718079280468056708, 465170595718079289289288630, 25223171, 4096, [], 465322134529441100226870706, 465322134529441109050975489⟩
def PrimData50.s24 : Seg := ⟨465322134529441100226870706, 465322134529441109050975489, 25231363, 4096, [], 465465187425980302592840395, 465465187425980311419656981⟩
def PrimData50.s25 : Seg := ⟨465465187425980302592840395, 465465187425980311419656981, 25239555, 4096, [], 465613587941576948814892173, 465613587941576957644521990⟩
def PrimData50.s26 : Seg := ⟨465613587941576948814892173, 465613587941576957644521990, 25247747, 4096, [], 465759161590844495107234910, 465759161590844503939625382⟩
def PrimData50.s27 : Seg := ⟨465759161590844495107234910, 465759161590844503939625382, 25255939, 4096, [], 465917000348062311310240843, 465917000348062320145623701⟩
def PrimData50.s28 : Seg := ⟨465917000348062311310240843, 465917000348062320145623701, 25264131, 4096, [], 466069496939309002387227285, 466069496939309011225501402⟩
def PrimData50.s29 : Seg := ⟨466069496939309002387227285, 466069496939309011225501402, 25272323, 4096, [], 466221681873390978853745213, 466221681873390987694905023⟩
def PrimData50.s30 : Seg := ⟨466221681873390978853745213, 466221681873390987694905023, 25280515, 4096, [], 466369782080885732496474791, 466369782080885741340442841⟩
def PrimData50.s31 : Seg := ⟨466369782080885732496474791, 466369782080885741340442841, 25288707, 4096, [], 466513168426972362827635242, 466513168426972371674321648⟩
def PrimData50.s32 : Seg := ⟨466513168426972362827635242, 466513168426972371674321648, 25296899, 4096, [], 466672594431632002425102290, 466672594431632011274812029⟩
def PrimData50.s33 : Seg := ⟨466672594431632002425102290, 466672594431632011274812029, 25305091, 4096, [], 466824162066271349272681723, 466824162066271358125265602⟩
def PrimData50.s34 : Seg := ⟨466824162066271349272681723, 466824162066271358125265602, 25313283, 4096, [], 466977304894593741773874007, 466977304894593750629361814⟩

def PrimData50.segs : List Seg := [PrimData50.s0, PrimData50.s1, PrimData50.s2, PrimData50.s3, PrimData50.s4, PrimData50.s5, PrimData50.s6, PrimData50.s7, PrimData50.s8, PrimData50.s9, PrimData50.s10, PrimData50.s11, PrimData50.s12, PrimData50.s13, PrimData50.s14, PrimData50.s15, PrimData50.s16, PrimData50.s17, PrimData50.s18, PrimData50.s19, PrimData50.s20, PrimData50.s21, PrimData50.s22, PrimData50.s23, PrimData50.s24, PrimData50.s25, PrimData50.s26, PrimData50.s27, PrimData50.s28, PrimData50.s29, PrimData50.s30, PrimData50.s31, PrimData50.s32, PrimData50.s33, PrimData50.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked50_s0 : Seg.bok PrimData50.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s0

theorem checked50_s1 : Seg.bok PrimData50.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s1

theorem checked50_s2 : Seg.bok PrimData50.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s2

theorem checked50_s3 : Seg.bok PrimData50.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s3

theorem checked50_s4 : Seg.bok PrimData50.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s4

theorem checked50_s5 : Seg.bok PrimData50.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s5

theorem checked50_s6 : Seg.bok PrimData50.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s6

theorem checked50_s7 : Seg.bok PrimData50.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s7

theorem checked50_s8 : Seg.bok PrimData50.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s8

theorem checked50_s9 : Seg.bok PrimData50.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s9

theorem checked50_s10 : Seg.bok PrimData50.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s10

theorem checked50_s11 : Seg.bok PrimData50.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s11

theorem checked50_s12 : Seg.bok PrimData50.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s12

theorem checked50_s13 : Seg.bok PrimData50.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s13

theorem checked50_s14 : Seg.bok PrimData50.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s14

theorem checked50_s15 : Seg.bok PrimData50.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s15

theorem checked50_s16 : Seg.bok PrimData50.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s16

theorem checked50_s17 : Seg.bok PrimData50.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s17

theorem checked50_s18 : Seg.bok PrimData50.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s18

theorem checked50_s19 : Seg.bok PrimData50.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s19

theorem checked50_s20 : Seg.bok PrimData50.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s20

theorem checked50_s21 : Seg.bok PrimData50.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s21

theorem checked50_s22 : Seg.bok PrimData50.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s22

theorem checked50_s23 : Seg.bok PrimData50.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s23

theorem checked50_s24 : Seg.bok PrimData50.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s24

theorem checked50_s25 : Seg.bok PrimData50.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s25

theorem checked50_s26 : Seg.bok PrimData50.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s26

theorem checked50_s27 : Seg.bok PrimData50.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s27

theorem checked50_s28 : Seg.bok PrimData50.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s28

theorem checked50_s29 : Seg.bok PrimData50.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s29

theorem checked50_s30 : Seg.bok PrimData50.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s30

theorem checked50_s31 : Seg.bok PrimData50.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s31

theorem checked50_s32 : Seg.bok PrimData50.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s32

theorem checked50_s33 : Seg.bok PrimData50.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s33

theorem checked50_s34 : Seg.bok PrimData50.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50_s34

 theorem checked50 : ∀ s ∈ PrimData50.segs, (Seg.bok s) = true := by
  unfold PrimData50.segs
  exact List.forall_mem_cons.2 ⟨checked50_s0, List.forall_mem_cons.2 ⟨checked50_s1, List.forall_mem_cons.2 ⟨checked50_s2, List.forall_mem_cons.2 ⟨checked50_s3, List.forall_mem_cons.2 ⟨checked50_s4, List.forall_mem_cons.2 ⟨checked50_s5, List.forall_mem_cons.2 ⟨checked50_s6, List.forall_mem_cons.2 ⟨checked50_s7, List.forall_mem_cons.2 ⟨checked50_s8, List.forall_mem_cons.2 ⟨checked50_s9, List.forall_mem_cons.2 ⟨checked50_s10, List.forall_mem_cons.2 ⟨checked50_s11, List.forall_mem_cons.2 ⟨checked50_s12, List.forall_mem_cons.2 ⟨checked50_s13, List.forall_mem_cons.2 ⟨checked50_s14, List.forall_mem_cons.2 ⟨checked50_s15, List.forall_mem_cons.2 ⟨checked50_s16, List.forall_mem_cons.2 ⟨checked50_s17, List.forall_mem_cons.2 ⟨checked50_s18, List.forall_mem_cons.2 ⟨checked50_s19, List.forall_mem_cons.2 ⟨checked50_s20, List.forall_mem_cons.2 ⟨checked50_s21, List.forall_mem_cons.2 ⟨checked50_s22, List.forall_mem_cons.2 ⟨checked50_s23, List.forall_mem_cons.2 ⟨checked50_s24, List.forall_mem_cons.2 ⟨checked50_s25, List.forall_mem_cons.2 ⟨checked50_s26, List.forall_mem_cons.2 ⟨checked50_s27, List.forall_mem_cons.2 ⟨checked50_s28, List.forall_mem_cons.2 ⟨checked50_s29, List.forall_mem_cons.2 ⟨checked50_s30, List.forall_mem_cons.2 ⟨checked50_s31, List.forall_mem_cons.2 ⟨checked50_s32, List.forall_mem_cons.2 ⟨checked50_s33, List.forall_mem_singleton.2 checked50_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked50
