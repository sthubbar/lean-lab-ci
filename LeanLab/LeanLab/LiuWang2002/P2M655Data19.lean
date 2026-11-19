/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_19.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/f08a2a90-0753-479b-9dde-f2d413a185b3
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData19.s0 : Seg := ⟨297761828040368847247783066, 297761828040368852894441779, 16146435, 4096, [], 297908176869935171977725717, 297908176869935177627157662⟩
def PrimData19.s1 : Seg := ⟨297908176869935171977725717, 297908176869935177627157662, 16154627, 4096, [], 298053305493276291518788955, 298053305493276297170970804⟩
def PrimData19.s2 : Seg := ⟨298053305493276291518788955, 298053305493276297170970804, 16162819, 4096, [], 298207011813813624490254968, 298207011813813630145350024⟩
def PrimData19.s3 : Seg := ⟨298207011813813624490254968, 298207011813813630145350024, 16171011, 4096, [], 298349699685194262155119812, 298349699685194267812918118⟩
def PrimData19.s4 : Seg := ⟨298349699685194262155119812, 298349699685194267812918118, 16179203, 4096, [], 298500659438398072607381256, 298500659438398078268040275⟩
def PrimData19.s5 : Seg := ⟨298500659438398072607381256, 298500659438398078268040275, 16187395, 4096, [], 298658666870178269715364450, 298658666870178275379018319⟩
def PrimData19.s6 : Seg := ⟨298658666870178269715364450, 298658666870178275379018319, 16195587, 4096, [], 298807798556829809235454204, 298807798556829814901933803⟩
def PrimData19.s7 : Seg := ⟨298807798556829809235454204, 298807798556829814901933803, 16203779, 4096, [], 298964284348961870163120908, 298964284348961875832566243⟩
def PrimData19.s8 : Seg := ⟨298964284348961870163120908, 298964284348961875832566243, 16211971, 4096, [], 299119243738013930948642293, 299119243738013936621024166⟩
def PrimData19.s9 : Seg := ⟨299119243738013930948642293, 299119243738013936621024166, 16220163, 4096, [], 299268082803196776971160965, 299268082803196782646362726⟩
def PrimData19.s10 : Seg := ⟨299268082803196776971160965, 299268082803196782646362726, 16228355, 4096, [], 299419682793549998877940635, 299419682793550004556014774⟩
def PrimData19.s11 : Seg := ⟨299419682793549998877940635, 299419682793550004556014774, 16236547, 4096, [], 299573124937908736665564351, 299573124937908742346545868⟩
def PrimData19.s12 : Seg := ⟨299573124937908736665564351, 299573124937908742346545868, 16244739, 4096, [], 299720446147124066910834633, 299720446147124072594606880⟩
def PrimData19.s13 : Seg := ⟨299720446147124066910834633, 299720446147124072594606880, 16252931, 4096, [], 299874203919050174957850447, 299874203919050180644535894⟩
def PrimData19.s14 : Seg := ⟨299874203919050174957850447, 299874203919050180644535894, 16261123, 4096, [], 300031948301511054249388333, 300031948301511059939062798⟩
def PrimData19.s15 : Seg := ⟨300031948301511054249388333, 300031948301511059939062798, 16269315, 4096, [], 300180508152022129070725352, 300180508152022134763213877⟩
def PrimData19.s16 : Seg := ⟨300180508152022129070725352, 300180508152022134763213877, 16277507, 4096, [], 300325396704221626815773788, 300325396704221632511006388⟩
def PrimData19.s17 : Seg := ⟨300325396704221626815773788, 300325396704221632511006388, 16285699, 4096, [], 300481011070155275914365024, 300481011070155281612545819⟩
def PrimData19.s18 : Seg := ⟨300481011070155275914365024, 300481011070155281612545819, 16293891, 4096, [], 300632035096361694449801855, 300632035096361700150843380⟩
def PrimData19.s19 : Seg := ⟨300632035096361694449801855, 300632035096361700150843380, 16302083, 4096, [], 300788271589863974712081696, 300788271589863980416083092⟩
def PrimData19.s20 : Seg := ⟨300788271589863974712081696, 300788271589863980416083092, 16310275, 4096, [], 300933177655066749232733339, 300933177655066754939478811⟩
def PrimData19.s21 : Seg := ⟨300933177655066749232733339, 300933177655066754939478811, 16318467, 4096, [], 301076249905923531059144312, 301076249905923536768598878⟩
def PrimData19.s22 : Seg := ⟨301076249905923531059144312, 301076249905923536768598878, 16326659, 4096, [], 301224534824291986135215821, 301224534824291991847478622⟩
def PrimData19.s23 : Seg := ⟨301224534824291986135215821, 301224534824291991847478622, 16334851, 4096, [], 301373130646033310513847273, 301373130646033316228924142⟩
def PrimData19.s24 : Seg := ⟨301373130646033310513847273, 301373130646033316228924142, 16343043, 4096, [], 301526326881741449505834857, 301526326881741455223813266⟩
def PrimData19.s25 : Seg := ⟨301526326881741449505834857, 301526326881741455223813266, 16351235, 4096, [], 301675850921015765448945146, 301675850921015771169755110⟩
def PrimData19.s26 : Seg := ⟨301675850921015765448945146, 301675850921015771169755110, 16359427, 4096, [], 301825379457465599903059966, 301825379457465605626701497⟩
def PrimData19.s27 : Seg := ⟨301825379457465599903059966, 301825379457465605626701497, 16367619, 4096, [], 301974299624166401144455489, 301974299624166406870916916⟩
def PrimData19.s28 : Seg := ⟨301974299624166401144455489, 301974299624166406870916916, 16375811, 4096, [], 302125062814710605797616177, 302125062814710611526932504⟩
def PrimData19.s29 : Seg := ⟨302125062814710605797616177, 302125062814710611526932504, 16384003, 4096, [], 302278894946081002907097068, 302278894946081008639326621⟩
def PrimData19.s30 : Seg := ⟨302278894946081002907097068, 302278894946081008639326621, 16392195, 4096, [], 302427215624850973830160433, 302427215624850979565198216⟩
def PrimData19.s31 : Seg := ⟨302427215624850973830160433, 302427215624850979565198216, 16400387, 4096, [], 302578605327050683996342682, 302578605327050689734247044⟩
def PrimData19.s32 : Seg := ⟨302578605327050683996342682, 302578605327050689734247044, 16408579, 4096, [], 302733064291664112799965987, 302733064291664118540795263⟩
def PrimData19.s33 : Seg := ⟨302733064291664112799965987, 302733064291664118540795263, 16416771, 4096, [], 302890899226278247092421082, 302890899226278252836239416⟩
def PrimData19.s34 : Seg := ⟨302890899226278247092421082, 302890899226278252836239416, 16424963, 4096, [], 303038931286996925069001588, 303038931286996930815622342⟩

def PrimData19.segs : List Seg := [PrimData19.s0, PrimData19.s1, PrimData19.s2, PrimData19.s3, PrimData19.s4, PrimData19.s5, PrimData19.s6, PrimData19.s7, PrimData19.s8, PrimData19.s9, PrimData19.s10, PrimData19.s11, PrimData19.s12, PrimData19.s13, PrimData19.s14, PrimData19.s15, PrimData19.s16, PrimData19.s17, PrimData19.s18, PrimData19.s19, PrimData19.s20, PrimData19.s21, PrimData19.s22, PrimData19.s23, PrimData19.s24, PrimData19.s25, PrimData19.s26, PrimData19.s27, PrimData19.s28, PrimData19.s29, PrimData19.s30, PrimData19.s31, PrimData19.s32, PrimData19.s33, PrimData19.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked19_s0 : Seg.bok PrimData19.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s0

theorem checked19_s1 : Seg.bok PrimData19.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s1

theorem checked19_s2 : Seg.bok PrimData19.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s2

theorem checked19_s3 : Seg.bok PrimData19.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s3

theorem checked19_s4 : Seg.bok PrimData19.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s4

theorem checked19_s5 : Seg.bok PrimData19.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s5

theorem checked19_s6 : Seg.bok PrimData19.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s6

theorem checked19_s7 : Seg.bok PrimData19.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s7

theorem checked19_s8 : Seg.bok PrimData19.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s8

theorem checked19_s9 : Seg.bok PrimData19.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s9

theorem checked19_s10 : Seg.bok PrimData19.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s10

theorem checked19_s11 : Seg.bok PrimData19.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s11

theorem checked19_s12 : Seg.bok PrimData19.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s12

theorem checked19_s13 : Seg.bok PrimData19.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s13

theorem checked19_s14 : Seg.bok PrimData19.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s14

theorem checked19_s15 : Seg.bok PrimData19.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s15

theorem checked19_s16 : Seg.bok PrimData19.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s16

theorem checked19_s17 : Seg.bok PrimData19.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s17

theorem checked19_s18 : Seg.bok PrimData19.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s18

theorem checked19_s19 : Seg.bok PrimData19.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s19

theorem checked19_s20 : Seg.bok PrimData19.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s20

theorem checked19_s21 : Seg.bok PrimData19.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s21

theorem checked19_s22 : Seg.bok PrimData19.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s22

theorem checked19_s23 : Seg.bok PrimData19.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s23

theorem checked19_s24 : Seg.bok PrimData19.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s24

theorem checked19_s25 : Seg.bok PrimData19.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s25

theorem checked19_s26 : Seg.bok PrimData19.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s26

theorem checked19_s27 : Seg.bok PrimData19.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s27

theorem checked19_s28 : Seg.bok PrimData19.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s28

theorem checked19_s29 : Seg.bok PrimData19.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s29

theorem checked19_s30 : Seg.bok PrimData19.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s30

theorem checked19_s31 : Seg.bok PrimData19.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s31

theorem checked19_s32 : Seg.bok PrimData19.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s32

theorem checked19_s33 : Seg.bok PrimData19.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s33

theorem checked19_s34 : Seg.bok PrimData19.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19_s34

 theorem checked19 : ∀ s ∈ PrimData19.segs, (Seg.bok s) = true := by
  unfold PrimData19.segs
  exact List.forall_mem_cons.2 ⟨checked19_s0, List.forall_mem_cons.2 ⟨checked19_s1, List.forall_mem_cons.2 ⟨checked19_s2, List.forall_mem_cons.2 ⟨checked19_s3, List.forall_mem_cons.2 ⟨checked19_s4, List.forall_mem_cons.2 ⟨checked19_s5, List.forall_mem_cons.2 ⟨checked19_s6, List.forall_mem_cons.2 ⟨checked19_s7, List.forall_mem_cons.2 ⟨checked19_s8, List.forall_mem_cons.2 ⟨checked19_s9, List.forall_mem_cons.2 ⟨checked19_s10, List.forall_mem_cons.2 ⟨checked19_s11, List.forall_mem_cons.2 ⟨checked19_s12, List.forall_mem_cons.2 ⟨checked19_s13, List.forall_mem_cons.2 ⟨checked19_s14, List.forall_mem_cons.2 ⟨checked19_s15, List.forall_mem_cons.2 ⟨checked19_s16, List.forall_mem_cons.2 ⟨checked19_s17, List.forall_mem_cons.2 ⟨checked19_s18, List.forall_mem_cons.2 ⟨checked19_s19, List.forall_mem_cons.2 ⟨checked19_s20, List.forall_mem_cons.2 ⟨checked19_s21, List.forall_mem_cons.2 ⟨checked19_s22, List.forall_mem_cons.2 ⟨checked19_s23, List.forall_mem_cons.2 ⟨checked19_s24, List.forall_mem_cons.2 ⟨checked19_s25, List.forall_mem_cons.2 ⟨checked19_s26, List.forall_mem_cons.2 ⟨checked19_s27, List.forall_mem_cons.2 ⟨checked19_s28, List.forall_mem_cons.2 ⟨checked19_s29, List.forall_mem_cons.2 ⟨checked19_s30, List.forall_mem_cons.2 ⟨checked19_s31, List.forall_mem_cons.2 ⟨checked19_s32, List.forall_mem_cons.2 ⟨checked19_s33, List.forall_mem_singleton.2 checked19_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked19
