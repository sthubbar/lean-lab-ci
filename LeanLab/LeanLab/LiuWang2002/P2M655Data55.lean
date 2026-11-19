/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_55.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/d1c811d7-f18b-4b9b-ab2c-8f4d85c0d7cb
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData55.s0 : Seg := ⟨488138870868306132919997298, 488138870868306142176765526, 26468355, 4096, [], 488295252049873274347834915, 488295252049873283607568261⟩
def PrimData55.s1 : Seg := ⟨488295252049873274347834915, 488295252049873283607568261, 26476547, 4096, [], 488444069144036735732065845, 488444069144036744994619387⟩
def PrimData55.s2 : Seg := ⟨488444069144036735732065845, 488444069144036744994619387, 26484739, 4096, [], 488596987748615253829261947, 488596987748615263094713821⟩
def PrimData55.s3 : Seg := ⟨488596987748615253829261947, 488596987748615263094713821, 26492931, 4096, [], 488750539733163611754741324, 488750539733163621023104442⟩
def PrimData55.s4 : Seg := ⟨488750539733163611754741324, 488750539733163621023104442, 26501123, 4096, [], 488908824086784014759823557, 488908824086784024031186939⟩
def PrimData55.s5 : Seg := ⟨488908824086784014759823557, 488908824086784024031186939, 26509315, 4096, [], 489055759999317593442195402, 489055759999317602716344135⟩
def PrimData55.s6 : Seg := ⟨489055759999317593442195402, 489055759999317602716344135, 26517507, 4096, [], 489202698581782823841602849, 489202698581782833118536954⟩
def PrimData55.s7 : Seg := ⟨489202698581782823841602849, 489202698581782833118536954, 26525699, 4096, [], 489359730220261858015501851, 489359730220261867295412839⟩
def PrimData55.s8 : Seg := ⟨489359730220261858015501851, 489359730220261867295412839, 26533891, 4096, [], 489512034732228373495927947, 489512034732228382778726217⟩
def PrimData55.s9 : Seg := ⟨489512034732228373495927947, 489512034732228382778726217, 26542083, 4096, [], 489667495374709687562730627, 489667495374709696848476337⟩
def PrimData55.s10 : Seg := ⟨489667495374709687562730627, 489667495374709696848476337, 26550275, 4096, [], 489821697480796020304809043, 489821697480796029593478152⟩
def PrimData55.s11 : Seg := ⟨489821697480796020304809043, 489821697480796029593478152, 26558467, 4096, [], 489975586986066550057820973, 489975586986066559349407908⟩
def PrimData55.s12 : Seg := ⟨489975586986066550057820973, 489975586986066559349407908, 26566659, 4096, [], 490120018697370426707935678, 490120018697370436002261023⟩
def PrimData55.s13 : Seg := ⟨490120018697370426707935678, 490120018697370436002261023, 26574851, 4096, [], 490268868029922686271642885, 490268868029922695568790475⟩
def PrimData55.s14 : Seg := ⟨490268868029922686271642885, 490268868029922695568790475, 26583043, 4096, [], 490425288754575875596330266, 490425288754575884896444492⟩
def PrimData55.s15 : Seg := ⟨490425288754575875596330266, 490425288754575884896444492, 26591235, 4096, [], 490576035636682454995382781, 490576035636682464298356403⟩
def PrimData55.s16 : Seg := ⟨490576035636682454995382781, 490576035636682464298356403, 26599427, 4096, [], 490721423856974368862603937, 490721423856974378168334180⟩
def PrimData55.s17 : Seg := ⟨490721423856974368862603937, 490721423856974378168334180, 26607619, 4096, [], 490869337755626445202998437, 490869337755626454511533611⟩
def PrimData55.s18 : Seg := ⟨490869337755626445202998437, 490869337755626454511533611, 26615811, 4096, [], 491021985106953060247046102, 491021985106953069558476759⟩
def PrimData55.s19 : Seg := ⟨491021985106953060247046102, 491021985106953069558476759, 26624003, 4096, [], 491175581396067548728159817, 491175581396067558042504570⟩
def PrimData55.s20 : Seg := ⟨491175581396067548728159817, 491175581396067558042504570, 26632195, 4096, [], 491327603465622759923452070, 491327603465622769240681106⟩
def PrimData55.s21 : Seg := ⟨491327603465622759923452070, 491327603465622769240681106, 26640387, 4096, [], 491479943636377212454368504, 491479943636377221774488870⟩
def PrimData55.s22 : Seg := ⟨491479943636377212454368504, 491479943636377221774488870, 26648579, 4096, [], 491632602018706324062999054, 491632602018706333386016096⟩
def PrimData55.s23 : Seg := ⟨491632602018706324062999054, 491632602018706333386016096, 26656771, 4096, [], 491782739813068665874462284, 491782739813068675200328860⟩
def PrimData55.s24 : Seg := ⟨491782739813068665874462284, 491782739813068675200328860, 26664963, 4096, [], 491937611572117579301749610, 491937611572117588630554901⟩
def PrimData55.s25 : Seg := ⟨491937611572117579301749610, 491937611572117588630554901, 26673155, 4096, [], 492087123937137298715690914, 492087123937137308047333589⟩
def PrimData55.s26 : Seg := ⟨492087123937137298715690914, 492087123937137308047333589, 26681347, 4096, [], 492237585180989550833677891, 492237585180989560168175203⟩
def PrimData55.s27 : Seg := ⟨492237585180989550833677891, 492237585180989560168175203, 26689539, 4096, [], 492386156602700761214420061, 492386156602700770551736532⟩
def PrimData55.s28 : Seg := ⟨492386156602700761214420061, 492386156602700770551736532, 26697731, 4096, [], 492531260733811210653953988, 492531260733811219994023036⟩
def PrimData55.s29 : Seg := ⟨492531260733811210653953988, 492531260733811219994023036, 26705923, 4096, [], 492695925334335554796652204, 492695925334335564139846105⟩
def PrimData55.s30 : Seg := ⟨492695925334335554796652204, 492695925334335564139846105, 26714115, 4096, [], 492841981023260342432944602, 492841981023260351778909791⟩
def PrimData55.s31 : Seg := ⟨492841981023260342432944602, 492841981023260351778909791, 26722307, 4096, [], 492985831129070534014310959, 492985831129070543363004425⟩
def PrimData55.s32 : Seg := ⟨492985831129070534014310959, 492985831129070543363004425, 26730499, 4096, [], 493137570503575512872511944, 493137570503575522224084104⟩
def PrimData55.s33 : Seg := ⟨493137570503575512872511944, 493137570503575522224084104, 26738691, 4096, [], 493283949561323873964682878, 493283949561323883319031186⟩
def PrimData55.s34 : Seg := ⟨493283949561323873964682878, 493283949561323883319031186, 26746883, 4096, [], 493431908623237641195813668, 493431908623237650552969471⟩

def PrimData55.segs : List Seg := [PrimData55.s0, PrimData55.s1, PrimData55.s2, PrimData55.s3, PrimData55.s4, PrimData55.s5, PrimData55.s6, PrimData55.s7, PrimData55.s8, PrimData55.s9, PrimData55.s10, PrimData55.s11, PrimData55.s12, PrimData55.s13, PrimData55.s14, PrimData55.s15, PrimData55.s16, PrimData55.s17, PrimData55.s18, PrimData55.s19, PrimData55.s20, PrimData55.s21, PrimData55.s22, PrimData55.s23, PrimData55.s24, PrimData55.s25, PrimData55.s26, PrimData55.s27, PrimData55.s28, PrimData55.s29, PrimData55.s30, PrimData55.s31, PrimData55.s32, PrimData55.s33, PrimData55.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked55_s0 : Seg.bok PrimData55.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s0

theorem checked55_s1 : Seg.bok PrimData55.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s1

theorem checked55_s2 : Seg.bok PrimData55.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s2

theorem checked55_s3 : Seg.bok PrimData55.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s3

theorem checked55_s4 : Seg.bok PrimData55.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s4

theorem checked55_s5 : Seg.bok PrimData55.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s5

theorem checked55_s6 : Seg.bok PrimData55.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s6

theorem checked55_s7 : Seg.bok PrimData55.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s7

theorem checked55_s8 : Seg.bok PrimData55.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s8

theorem checked55_s9 : Seg.bok PrimData55.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s9

theorem checked55_s10 : Seg.bok PrimData55.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s10

theorem checked55_s11 : Seg.bok PrimData55.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s11

theorem checked55_s12 : Seg.bok PrimData55.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s12

theorem checked55_s13 : Seg.bok PrimData55.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s13

theorem checked55_s14 : Seg.bok PrimData55.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s14

theorem checked55_s15 : Seg.bok PrimData55.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s15

theorem checked55_s16 : Seg.bok PrimData55.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s16

theorem checked55_s17 : Seg.bok PrimData55.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s17

theorem checked55_s18 : Seg.bok PrimData55.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s18

theorem checked55_s19 : Seg.bok PrimData55.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s19

theorem checked55_s20 : Seg.bok PrimData55.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s20

theorem checked55_s21 : Seg.bok PrimData55.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s21

theorem checked55_s22 : Seg.bok PrimData55.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s22

theorem checked55_s23 : Seg.bok PrimData55.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s23

theorem checked55_s24 : Seg.bok PrimData55.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s24

theorem checked55_s25 : Seg.bok PrimData55.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s25

theorem checked55_s26 : Seg.bok PrimData55.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s26

theorem checked55_s27 : Seg.bok PrimData55.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s27

theorem checked55_s28 : Seg.bok PrimData55.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s28

theorem checked55_s29 : Seg.bok PrimData55.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s29

theorem checked55_s30 : Seg.bok PrimData55.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s30

theorem checked55_s31 : Seg.bok PrimData55.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s31

theorem checked55_s32 : Seg.bok PrimData55.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s32

theorem checked55_s33 : Seg.bok PrimData55.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s33

theorem checked55_s34 : Seg.bok PrimData55.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55_s34

 theorem checked55 : ∀ s ∈ PrimData55.segs, (Seg.bok s) = true := by
  unfold PrimData55.segs
  exact List.forall_mem_cons.2 ⟨checked55_s0, List.forall_mem_cons.2 ⟨checked55_s1, List.forall_mem_cons.2 ⟨checked55_s2, List.forall_mem_cons.2 ⟨checked55_s3, List.forall_mem_cons.2 ⟨checked55_s4, List.forall_mem_cons.2 ⟨checked55_s5, List.forall_mem_cons.2 ⟨checked55_s6, List.forall_mem_cons.2 ⟨checked55_s7, List.forall_mem_cons.2 ⟨checked55_s8, List.forall_mem_cons.2 ⟨checked55_s9, List.forall_mem_cons.2 ⟨checked55_s10, List.forall_mem_cons.2 ⟨checked55_s11, List.forall_mem_cons.2 ⟨checked55_s12, List.forall_mem_cons.2 ⟨checked55_s13, List.forall_mem_cons.2 ⟨checked55_s14, List.forall_mem_cons.2 ⟨checked55_s15, List.forall_mem_cons.2 ⟨checked55_s16, List.forall_mem_cons.2 ⟨checked55_s17, List.forall_mem_cons.2 ⟨checked55_s18, List.forall_mem_cons.2 ⟨checked55_s19, List.forall_mem_cons.2 ⟨checked55_s20, List.forall_mem_cons.2 ⟨checked55_s21, List.forall_mem_cons.2 ⟨checked55_s22, List.forall_mem_cons.2 ⟨checked55_s23, List.forall_mem_cons.2 ⟨checked55_s24, List.forall_mem_cons.2 ⟨checked55_s25, List.forall_mem_cons.2 ⟨checked55_s26, List.forall_mem_cons.2 ⟨checked55_s27, List.forall_mem_cons.2 ⟨checked55_s28, List.forall_mem_cons.2 ⟨checked55_s29, List.forall_mem_cons.2 ⟨checked55_s30, List.forall_mem_cons.2 ⟨checked55_s31, List.forall_mem_cons.2 ⟨checked55_s32, List.forall_mem_cons.2 ⟨checked55_s33, List.forall_mem_singleton.2 checked55_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked55
