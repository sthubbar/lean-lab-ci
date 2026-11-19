/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_32.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/0a78202c-0880-4bf7-8eed-29c383f4a96d
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData32.s0 : Seg := ⟨366523449551318007454215586, 366523449551318014404759915, 19873795, 4096, [], 366673799442326532470101099, 366673799442326539423495946⟩
def PrimData32.s1 : Seg := ⟨366673799442326532470101099, 366673799442326539423495946, 19881987, 4096, [], 366829113076822910015788985, 366829113076822916972129187⟩
def PrimData32.s2 : Seg := ⟨366829113076822910015788985, 366829113076822916972129187, 19890179, 4096, [], 366970789837526349688921772, 366970789837526356647948596⟩
def PrimData32.s3 : Seg := ⟨366970789837526349688921772, 366970789837526356647948596, 19898371, 4096, [], 367121770818192171161428672, 367121770818192178123318493⟩
def PrimData32.s4 : Seg := ⟨367121770818192171161428672, 367121770818192178123318493, 19906563, 4096, [], 367272445408369866217223011, 367272445408369873181970286⟩
def PrimData32.s5 : Seg := ⟨367272445408369866217223011, 367272445408369873181970286, 19914755, 4096, [], 367433044918604961657734385, 367433044918604968625527786⟩
def PrimData32.s6 : Seg := ⟨367433044918604961657734385, 367433044918604968625527786, 19922947, 4096, [], 367582486719191643368462857, 367582486719191650339090350⟩
def PrimData32.s7 : Seg := ⟨367582486719191643368462857, 367582486719191650339090350, 19931139, 4096, [], 367738753386148555812242107, 367738753386148562785833506⟩
def PrimData32.s8 : Seg := ⟨367738753386148555812242107, 367738753386148562785833506, 19939331, 4096, [], 367890683081936552587684552, 367890683081936559564157098⟩
def PrimData32.s9 : Seg := ⟨367890683081936552587684552, 367890683081936559564157098, 19947523, 4096, [], 368038895621484277402292220, 368038895621484284381576651⟩
def PrimData32.s10 : Seg := ⟨368038895621484277402292220, 368038895621484284381576651, 19955715, 4096, [], 368195173673829556292832942, 368195173673829563275082332⟩
def PrimData32.s11 : Seg := ⟨368195173673829556292832942, 368195173673829563275082332, 19963907, 4096, [], 368340292553917350966123901, 368340292553917357951126597⟩
def PrimData32.s12 : Seg := ⟨368340292553917350966123901, 368340292553917357951126597, 19972099, 4096, [], 368492547145782310561865254, 368492547145782317549756850⟩
def PrimData32.s13 : Seg := ⟨368492547145782310561865254, 368492547145782317549756850, 19980291, 4096, [], 368642634715596875487358141, 368642634715596882478096598⟩
def PrimData32.s14 : Seg := ⟨368642634715596875487358141, 368642634715596882478096598, 19988483, 4096, [], 368798617953368675255104968, 368798617953368682248803038⟩
def PrimData32.s15 : Seg := ⟨368798617953368675255104968, 368798617953368682248803038, 19996675, 4096, [], 368947472376666186102828096, 368947472376666193099349213⟩
def PrimData32.s16 : Seg := ⟨368947472376666186102828096, 368947472376666193099349213, 20004867, 4096, [], 369095400026376767974577116, 369095400026376774973905242⟩
def PrimData32.s17 : Seg := ⟨369095400026376767974577116, 369095400026376774973905242, 20013059, 4096, [], 369250774363200658284558257, 369250774363200665286833846⟩
def PrimData32.s18 : Seg := ⟨369250774363200658284558257, 369250774363200665286833846, 20021251, 4096, [], 369407082968303228814871315, 369407082968303235820111620⟩
def PrimData32.s19 : Seg := ⟨369407082968303228814871315, 369407082968303235820111620, 20029443, 4096, [], 369559673602481969137126272, 369559673602481976145261066⟩
def PrimData32.s20 : Seg := ⟨369559673602481969137126272, 369559673602481976145261066, 20037635, 4096, [], 369711027372481069187508229, 369711027372481076198513698⟩
def PrimData32.s21 : Seg := ⟨369711027372481069187508229, 369711027372481076198513698, 20045827, 4096, [], 369860213692534989449552628, 369860213692534996463387219⟩
def PrimData32.s22 : Seg := ⟨369860213692534989449552628, 369860213692534996463387219, 20054019, 4096, [], 370011264630363568874555178, 370011264630363575891254612⟩
def PrimData32.s23 : Seg := ⟨370011264630363568874555178, 370011264630363575891254612, 20062211, 4096, [], 370162319222821638992614520, 370162319222821646012178314⟩
def PrimData32.s24 : Seg := ⟨370162319222821638992614520, 370162319222821646012178314, 20070403, 4096, [], 370317720034909059961010594, 370317720034909066983522339⟩
def PrimData32.s25 : Seg := ⟨370317720034909059961010594, 370317720034909066983522339, 20078595, 4096, [], 370467231040464954504100306, 370467231040464961529447254⟩
def PrimData32.s26 : Seg := ⟨370467231040464954504100306, 370467231040464961529447254, 20086787, 4096, [], 370618606861207169211232911, 370618606861207176239451516⟩
def PrimData32.s27 : Seg := ⟨370618606861207169211232911, 370618606861207176239451516, 20094979, 4096, [], 370768435286965925318474556, 370768435286965932349534685⟩
def PrimData32.s28 : Seg := ⟨370768435286965925318474556, 370768435286965932349534685, 20103171, 4096, [], 370922920513275653285949845, 370922920513275660319938510⟩
def PrimData32.s29 : Seg := ⟨370922920513275653285949845, 370922920513275660319938510, 20111363, 4096, [], 371068723411239989046013843, 371068723411239996082766760⟩
def PrimData32.s30 : Seg := ⟨371068723411239989046013843, 371068723411239996082766760, 20119555, 4096, [], 371217011632015130915946887, 371217011632015137955513141⟩
def PrimData32.s31 : Seg := ⟨371217011632015130915946887, 371217011632015137955513141, 20127747, 4096, [], 371368405759755988141030339, 371368405759755995183466817⟩
def PrimData32.s32 : Seg := ⟨371368405759755988141030339, 371368405759755995183466817, 20135939, 4096, [], 371515770502751200130004867, 371515770502751207175235264⟩
def PrimData32.s33 : Seg := ⟨371515770502751200130004867, 371515770502751207175235264, 20144131, 4096, [], 371667171986504630508043229, 371667171986504637556143890⟩
def PrimData32.s34 : Seg := ⟨371667171986504630508043229, 371667171986504637556143890, 20152323, 4096, [], 371815164270101001444265379, 371815164270101008495171606⟩

def PrimData32.segs : List Seg := [PrimData32.s0, PrimData32.s1, PrimData32.s2, PrimData32.s3, PrimData32.s4, PrimData32.s5, PrimData32.s6, PrimData32.s7, PrimData32.s8, PrimData32.s9, PrimData32.s10, PrimData32.s11, PrimData32.s12, PrimData32.s13, PrimData32.s14, PrimData32.s15, PrimData32.s16, PrimData32.s17, PrimData32.s18, PrimData32.s19, PrimData32.s20, PrimData32.s21, PrimData32.s22, PrimData32.s23, PrimData32.s24, PrimData32.s25, PrimData32.s26, PrimData32.s27, PrimData32.s28, PrimData32.s29, PrimData32.s30, PrimData32.s31, PrimData32.s32, PrimData32.s33, PrimData32.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked32_s0 : Seg.bok PrimData32.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s0

theorem checked32_s1 : Seg.bok PrimData32.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s1

theorem checked32_s2 : Seg.bok PrimData32.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s2

theorem checked32_s3 : Seg.bok PrimData32.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s3

theorem checked32_s4 : Seg.bok PrimData32.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s4

theorem checked32_s5 : Seg.bok PrimData32.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s5

theorem checked32_s6 : Seg.bok PrimData32.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s6

theorem checked32_s7 : Seg.bok PrimData32.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s7

theorem checked32_s8 : Seg.bok PrimData32.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s8

theorem checked32_s9 : Seg.bok PrimData32.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s9

theorem checked32_s10 : Seg.bok PrimData32.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s10

theorem checked32_s11 : Seg.bok PrimData32.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s11

theorem checked32_s12 : Seg.bok PrimData32.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s12

theorem checked32_s13 : Seg.bok PrimData32.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s13

theorem checked32_s14 : Seg.bok PrimData32.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s14

theorem checked32_s15 : Seg.bok PrimData32.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s15

theorem checked32_s16 : Seg.bok PrimData32.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s16

theorem checked32_s17 : Seg.bok PrimData32.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s17

theorem checked32_s18 : Seg.bok PrimData32.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s18

theorem checked32_s19 : Seg.bok PrimData32.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s19

theorem checked32_s20 : Seg.bok PrimData32.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s20

theorem checked32_s21 : Seg.bok PrimData32.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s21

theorem checked32_s22 : Seg.bok PrimData32.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s22

theorem checked32_s23 : Seg.bok PrimData32.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s23

theorem checked32_s24 : Seg.bok PrimData32.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s24

theorem checked32_s25 : Seg.bok PrimData32.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s25

theorem checked32_s26 : Seg.bok PrimData32.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s26

theorem checked32_s27 : Seg.bok PrimData32.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s27

theorem checked32_s28 : Seg.bok PrimData32.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s28

theorem checked32_s29 : Seg.bok PrimData32.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s29

theorem checked32_s30 : Seg.bok PrimData32.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s30

theorem checked32_s31 : Seg.bok PrimData32.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s31

theorem checked32_s32 : Seg.bok PrimData32.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s32

theorem checked32_s33 : Seg.bok PrimData32.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s33

theorem checked32_s34 : Seg.bok PrimData32.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32_s34

 theorem checked32 : ∀ s ∈ PrimData32.segs, (Seg.bok s) = true := by
  unfold PrimData32.segs
  exact List.forall_mem_cons.2 ⟨checked32_s0, List.forall_mem_cons.2 ⟨checked32_s1, List.forall_mem_cons.2 ⟨checked32_s2, List.forall_mem_cons.2 ⟨checked32_s3, List.forall_mem_cons.2 ⟨checked32_s4, List.forall_mem_cons.2 ⟨checked32_s5, List.forall_mem_cons.2 ⟨checked32_s6, List.forall_mem_cons.2 ⟨checked32_s7, List.forall_mem_cons.2 ⟨checked32_s8, List.forall_mem_cons.2 ⟨checked32_s9, List.forall_mem_cons.2 ⟨checked32_s10, List.forall_mem_cons.2 ⟨checked32_s11, List.forall_mem_cons.2 ⟨checked32_s12, List.forall_mem_cons.2 ⟨checked32_s13, List.forall_mem_cons.2 ⟨checked32_s14, List.forall_mem_cons.2 ⟨checked32_s15, List.forall_mem_cons.2 ⟨checked32_s16, List.forall_mem_cons.2 ⟨checked32_s17, List.forall_mem_cons.2 ⟨checked32_s18, List.forall_mem_cons.2 ⟨checked32_s19, List.forall_mem_cons.2 ⟨checked32_s20, List.forall_mem_cons.2 ⟨checked32_s21, List.forall_mem_cons.2 ⟨checked32_s22, List.forall_mem_cons.2 ⟨checked32_s23, List.forall_mem_cons.2 ⟨checked32_s24, List.forall_mem_cons.2 ⟨checked32_s25, List.forall_mem_cons.2 ⟨checked32_s26, List.forall_mem_cons.2 ⟨checked32_s27, List.forall_mem_cons.2 ⟨checked32_s28, List.forall_mem_cons.2 ⟨checked32_s29, List.forall_mem_cons.2 ⟨checked32_s30, List.forall_mem_cons.2 ⟨checked32_s31, List.forall_mem_cons.2 ⟨checked32_s32, List.forall_mem_cons.2 ⟨checked32_s33, List.forall_mem_singleton.2 checked32_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked32
