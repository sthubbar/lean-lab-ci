/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_62.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/a42b694d-60e3-48c2-9c85-d54d154bec4a
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData62.s0 : Seg := ⟨525174521978339806412486561, 525174521978339816371589778, 28475395, 4096, [], 525320489669260323665625093, 525320489669260333627495513⟩
def PrimData62.s1 : Seg := ⟨525320489669260323665625093, 525320489669260333627495513, 28483587, 4096, [], 525478175414617839354558318, 525478175414617849319418538⟩
def PrimData62.s2 : Seg := ⟨525478175414617839354558318, 525478175414617849319418538, 28491779, 4096, [], 525640296813365464917297206, 525640296813365474885233217⟩
def PrimData62.s3 : Seg := ⟨525640296813365464917297206, 525640296813365474885233217, 28499971, 4096, [], 525796087970745605089299178, 525796087970745615060189287⟩
def PrimData62.s4 : Seg := ⟨525796087970745605089299178, 525796087970745615060189287, 28508163, 4096, [], 525948398535401833130347009, 525948398535401843104124409⟩
def PrimData62.s5 : Seg := ⟨525948398535401833130347009, 525948398535401843104124409, 28516355, 4096, [], 526097861708925229571852216, 526097861708925239548463400⟩
def PrimData62.s6 : Seg := ⟨526097861708925229571852216, 526097861708925239548463400, 28524547, 4096, [], 526249227390523872586409683, 526249227390523882565892118⟩
def PrimData62.s7 : Seg := ⟨526249227390523872586409683, 526249227390523882565892118, 28532739, 4096, [], 526394262198343336474398704, 526394262198343346456631815⟩
def PrimData62.s8 : Seg := ⟨526394262198343336474398704, 526394262198343346456631815, 28540931, 4096, [], 526544999571250690335230609, 526544999571250700320323023⟩
def PrimData62.s9 : Seg := ⟨526544999571250690335230609, 526544999571250700320323023, 28549123, 4096, [], 526698906252324524454192266, 526698906252324534442203049⟩
def PrimData62.s10 : Seg := ⟨526698906252324524454192266, 526698906252324534442203049, 28557315, 4096, [], 526846481771676844306418010, 526846481771676854297227385⟩
def PrimData62.s11 : Seg := ⟨526846481771676844306418010, 526846481771676854297227385, 28565507, 4096, [], 526997226667851951068618308, 526997226667851961062285157⟩
def PrimData62.s12 : Seg := ⟨526997226667851951068618308, 526997226667851961062285157, 28573699, 4096, [], 527147340708856027234033918, 527147340708856037230546337⟩
def PrimData62.s13 : Seg := ⟨527147340708856027234033918, 527147340708856037230546337, 28581891, 4096, [], 527305691493793484845731932, 527305691493793494845247020⟩
def PrimData62.s14 : Seg := ⟨527305691493793484845731932, 527305691493793494845247020, 28590083, 4096, [], 527458027481186805735740770, 527458027481186815738143511⟩
def PrimData62.s15 : Seg := ⟨527458027481186805735740770, 527458027481186815738143511, 28598275, 4096, [], 527600864719357507130437065, 527600864719357517135547650⟩
def PrimData62.s16 : Seg := ⟨527600864719357507130437065, 527600864719357517135547650, 28606467, 4096, [], 527753205798515328710580096, 527753205798515338718578560⟩
def PrimData62.s17 : Seg := ⟨527753205798515328710580096, 527753205798515338718578560, 28614659, 4096, [], 527907449782794356236621056, 527907449782794366247544201⟩
def PrimData62.s18 : Seg := ⟨527907449782794356236621056, 527907449782794366247544201, 28622851, 4096, [], 528061696321407692949043245, 528061696321407702962890714⟩
def PrimData62.s19 : Seg := ⟨528061696321407692949043245, 528061696321407702962890714, 28631043, 4096, [], 528211194424566398368325965, 528211194424566408385008065⟩
def PrimData62.s20 : Seg := ⟨528211194424566398368325965, 528211194424566408385008065, 28639235, 4096, [], 528365446117853244764028117, 528365446117853254783635236⟩
def PrimData62.s21 : Seg := ⟨528365446117853244764028117, 528365446117853254783635236, 28647427, 4096, [], 528516849676344812151132532, 528516849676344822173609817⟩
def PrimData62.s22 : Seg := ⟨528516849676344812151132532, 528516849676344822173609817, 28655619, 4096, [], 528666355263175137232379735, 528666355263175147257691275⟩
def PrimData62.s23 : Seg := ⟨528666355263175137232379735, 528666355263175147257691275, 28663811, 4096, [], 528816496840305480909330650, 528816496840305490937488046⟩
def PrimData62.s24 : Seg := ⟨528816496840305480909330650, 528816496840305490937488046, 28672003, 4096, [], 528967591175775804507617022, 528967591175775814538639428⟩
def PrimData62.s25 : Seg := ⟨528967591175775804507617022, 528967591175775814538639428, 28680195, 4096, [], 529126290396257205243803227, 529126290396257215277836036⟩
def PrimData62.s26 : Seg := ⟨529126290396257205243803227, 529126290396257215277836036, 28688387, 4096, [], 529266302813761753367207655, 529266302813761763403895468⟩
def PrimData62.s27 : Seg := ⟨529266302813761753367207655, 529266302813761763403895468, 28696579, 4096, [], 529411069183269795232685315, 529411069183269805272118038⟩
def PrimData62.s28 : Seg := ⟨529411069183269795232685315, 529411069183269805272118038, 28704771, 4096, [], 529560906454026963443848893, 529560906454026973486122809⟩
def PrimData62.s29 : Seg := ⟨529560906454026963443848893, 529560906454026973486122809, 28712963, 4096, [], 529714864423254168332580881, 529714864423254178377774297⟩
def PrimData62.s30 : Seg := ⟨529714864423254168332580881, 529714864423254178377774297, 28721155, 4096, [], 529866924238673229069397961, 529866924238673239117475058⟩
def PrimData62.s31 : Seg := ⟨529866924238673229069397961, 529866924238673239117475058, 28729347, 4096, [], 530018669762886765022527649, 530018669762886775073482884⟩
def PrimData62.s32 : Seg := ⟨530018669762886765022527649, 530018669762886775073482884, 28737539, 4096, [], 530175486623998056487318437, 530175486623998066541247882⟩
def PrimData62.s33 : Seg := ⟨530175486623998056487318437, 530175486623998066541247882, 28745731, 4096, [], 530327554016351262906817273, 530327554016351272963630840⟩
def PrimData62.s34 : Seg := ⟨530327554016351262906817273, 530327554016351272963630840, 28753923, 4096, [], 530468852286647568430227360, 530468852286647578489719982⟩

def PrimData62.segs : List Seg := [PrimData62.s0, PrimData62.s1, PrimData62.s2, PrimData62.s3, PrimData62.s4, PrimData62.s5, PrimData62.s6, PrimData62.s7, PrimData62.s8, PrimData62.s9, PrimData62.s10, PrimData62.s11, PrimData62.s12, PrimData62.s13, PrimData62.s14, PrimData62.s15, PrimData62.s16, PrimData62.s17, PrimData62.s18, PrimData62.s19, PrimData62.s20, PrimData62.s21, PrimData62.s22, PrimData62.s23, PrimData62.s24, PrimData62.s25, PrimData62.s26, PrimData62.s27, PrimData62.s28, PrimData62.s29, PrimData62.s30, PrimData62.s31, PrimData62.s32, PrimData62.s33, PrimData62.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked62_s0 : Seg.bok PrimData62.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s0

theorem checked62_s1 : Seg.bok PrimData62.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s1

theorem checked62_s2 : Seg.bok PrimData62.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s2

theorem checked62_s3 : Seg.bok PrimData62.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s3

theorem checked62_s4 : Seg.bok PrimData62.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s4

theorem checked62_s5 : Seg.bok PrimData62.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s5

theorem checked62_s6 : Seg.bok PrimData62.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s6

theorem checked62_s7 : Seg.bok PrimData62.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s7

theorem checked62_s8 : Seg.bok PrimData62.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s8

theorem checked62_s9 : Seg.bok PrimData62.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s9

theorem checked62_s10 : Seg.bok PrimData62.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s10

theorem checked62_s11 : Seg.bok PrimData62.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s11

theorem checked62_s12 : Seg.bok PrimData62.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s12

theorem checked62_s13 : Seg.bok PrimData62.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s13

theorem checked62_s14 : Seg.bok PrimData62.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s14

theorem checked62_s15 : Seg.bok PrimData62.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s15

theorem checked62_s16 : Seg.bok PrimData62.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s16

theorem checked62_s17 : Seg.bok PrimData62.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s17

theorem checked62_s18 : Seg.bok PrimData62.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s18

theorem checked62_s19 : Seg.bok PrimData62.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s19

theorem checked62_s20 : Seg.bok PrimData62.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s20

theorem checked62_s21 : Seg.bok PrimData62.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s21

theorem checked62_s22 : Seg.bok PrimData62.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s22

theorem checked62_s23 : Seg.bok PrimData62.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s23

theorem checked62_s24 : Seg.bok PrimData62.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s24

theorem checked62_s25 : Seg.bok PrimData62.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s25

theorem checked62_s26 : Seg.bok PrimData62.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s26

theorem checked62_s27 : Seg.bok PrimData62.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s27

theorem checked62_s28 : Seg.bok PrimData62.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s28

theorem checked62_s29 : Seg.bok PrimData62.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s29

theorem checked62_s30 : Seg.bok PrimData62.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s30

theorem checked62_s31 : Seg.bok PrimData62.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s31

theorem checked62_s32 : Seg.bok PrimData62.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s32

theorem checked62_s33 : Seg.bok PrimData62.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s33

theorem checked62_s34 : Seg.bok PrimData62.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62_s34

 theorem checked62 : ∀ s ∈ PrimData62.segs, (Seg.bok s) = true := by
  unfold PrimData62.segs
  exact List.forall_mem_cons.2 ⟨checked62_s0, List.forall_mem_cons.2 ⟨checked62_s1, List.forall_mem_cons.2 ⟨checked62_s2, List.forall_mem_cons.2 ⟨checked62_s3, List.forall_mem_cons.2 ⟨checked62_s4, List.forall_mem_cons.2 ⟨checked62_s5, List.forall_mem_cons.2 ⟨checked62_s6, List.forall_mem_cons.2 ⟨checked62_s7, List.forall_mem_cons.2 ⟨checked62_s8, List.forall_mem_cons.2 ⟨checked62_s9, List.forall_mem_cons.2 ⟨checked62_s10, List.forall_mem_cons.2 ⟨checked62_s11, List.forall_mem_cons.2 ⟨checked62_s12, List.forall_mem_cons.2 ⟨checked62_s13, List.forall_mem_cons.2 ⟨checked62_s14, List.forall_mem_cons.2 ⟨checked62_s15, List.forall_mem_cons.2 ⟨checked62_s16, List.forall_mem_cons.2 ⟨checked62_s17, List.forall_mem_cons.2 ⟨checked62_s18, List.forall_mem_cons.2 ⟨checked62_s19, List.forall_mem_cons.2 ⟨checked62_s20, List.forall_mem_cons.2 ⟨checked62_s21, List.forall_mem_cons.2 ⟨checked62_s22, List.forall_mem_cons.2 ⟨checked62_s23, List.forall_mem_cons.2 ⟨checked62_s24, List.forall_mem_cons.2 ⟨checked62_s25, List.forall_mem_cons.2 ⟨checked62_s26, List.forall_mem_cons.2 ⟨checked62_s27, List.forall_mem_cons.2 ⟨checked62_s28, List.forall_mem_cons.2 ⟨checked62_s29, List.forall_mem_cons.2 ⟨checked62_s30, List.forall_mem_cons.2 ⟨checked62_s31, List.forall_mem_cons.2 ⟨checked62_s32, List.forall_mem_cons.2 ⟨checked62_s33, List.forall_mem_singleton.2 checked62_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked62
