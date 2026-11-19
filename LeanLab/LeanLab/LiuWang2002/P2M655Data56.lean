/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_56.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/8117149a-459f-48ca-b27f-af851010a78d
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData56.s0 : Seg := ⟨493431908623237641195813668, 493431908623237650552969471, 26755075, 4096, [], 493576084556886349291138440, 493576084556886358651028838⟩
def PrimData56.s1 : Seg := ⟨493576084556886349291138440, 493576084556886358651028838, 26763267, 4096, [], 493734144542940564375588291, 493734144542940573738477911⟩
def PrimData56.s2 : Seg := ⟨493734144542940564375588291, 493734144542940573738477911, 26771459, 4096, [], 493876432621094554590218996, 493876432621094563955808219⟩
def PrimData56.s3 : Seg := ⟨493876432621094554590218996, 493876432621094563955808219, 26779651, 4096, [], 494032605280034146160881802, 494032605280034155529434283⟩
def PrimData56.s4 : Seg := ⟨494032605280034146160881802, 494032605280034155529434283, 26787843, 4096, [], 494186572166215190178727155, 494186572166215199550200855⟩
def PrimData56.s5 : Seg := ⟨494186572166215190178727155, 494186572166215199550200855, 26796035, 4096, [], 494336124652012776934524816, 494336124652012786308835900⟩
def PrimData56.s6 : Seg := ⟨494336124652012776934524816, 494336124652012786308835900, 26804227, 4096, [], 494484733245131076836268892, 494484733245131086213398892⟩
def PrimData56.s7 : Seg := ⟨494484733245131076836268892, 494484733245131086213398892, 26812419, 4096, [], 494641863597359059195417590, 494641863597359068575528830⟩
def PrimData56.s8 : Seg := ⟨494641863597359059195417590, 494641863597359068575528830, 26820611, 4096, [], 494786060126495994901107906, 494786060126496004283954713⟩
def PrimData56.s9 : Seg := ⟨494786060126495994901107906, 494786060126496004283954713, 26828803, 4096, [], 494939409751461878910862669, 494939409751461888296617816⟩
def PrimData56.s10 : Seg := ⟨494939409751461878910862669, 494939409751461888296617816, 26836995, 4096, [], 495088975619139066595455001, 495088975619139075984047532⟩
def PrimData56.s11 : Seg := ⟨495088975619139066595455001, 495088975619139075984047532, 26845187, 4096, [], 495242015138272661246588883, 495242015138272670638084651⟩
def PrimData56.s12 : Seg := ⟨495242015138272661246588883, 495242015138272670638084651, 26853379, 4096, [], 495394110738436768806861776, 495394110738436778201242799⟩
def PrimData56.s13 : Seg := ⟨495394110738436768806861776, 495394110738436778201242799, 26861571, 4096, [], 495545893506997523572925660, 495545893506997532970185134⟩
def PrimData56.s14 : Seg := ⟨495545893506997523572925660, 495545893506997532970185134, 26869763, 4096, [], 495700203464081930182973562, 495700203464081939583160087⟩
def PrimData56.s15 : Seg := ⟨495700203464081930182973562, 495700203464081939583160087, 26877955, 4096, [], 495854200610240235266391046, 495854200610240244669499276⟩
def PrimData56.s16 : Seg := ⟨495854200610240235266391046, 495854200610240244669499276, 26886147, 4096, [], 496003151303661082549476510, 496003151303661091955409245⟩
def PrimData56.s17 : Seg := ⟨496003151303661082549476510, 496003151303661091955409245, 26894339, 4096, [], 496155576009924482131578399, 496155576009924491540402221⟩
def PrimData56.s18 : Seg := ⟨496155576009924482131578399, 496155576009924491540402221, 26902531, 4096, [], 496306109958534941893280562, 496306109958534951304958778⟩
def PrimData56.s19 : Seg := ⟨496306109958534941893280562, 496306109958534951304958778, 26910723, 4096, [], 496457593298826615066704568, 496457593298826624481255403⟩
def PrimData56.s20 : Seg := ⟨496457593298826615066704568, 496457593298826624481255403, 26918915, 4096, [], 496609394912088991217882258, 496609394912089000635312030⟩
def PrimData56.s21 : Seg := ⟨496609394912088991217882258, 496609394912089000635312030, 26927107, 4096, [], 496764670918929884622488395, 496764670918929894042863449⟩
def PrimData56.s22 : Seg := ⟨496764670918929884622488395, 496764670918929894042863449, 26935299, 4096, [], 496912059463492978420838197, 496912059463492987844008839⟩
def PrimData56.s23 : Seg := ⟨496912059463492978420838197, 496912059463492987844008839, 26943491, 4096, [], 497063869242798057902867024, 497063869242798067328916603⟩
def PrimData56.s24 : Seg := ⟨497063869242798057902867024, 497063869242798067328916603, 26951683, 4096, [], 497213788004264501536894171, 497213788004264510965786969⟩
def PrimData56.s25 : Seg := ⟨497213788004264501536894171, 497213788004264510965786969, 26959875, 4096, [], 497372862468299923899130018, 497372862468299933331039298⟩
def PrimData56.s26 : Seg := ⟨497372862468299923899130018, 497372862468299933331039298, 26968067, 4096, [], 497524049083176227442095840, 497524049083176236876871679⟩
def PrimData56.s27 : Seg := ⟨497524049083176227442095840, 497524049083176236876871679, 26976259, 4096, [], 497675238397130228633804515, 497675238397130238071446916⟩
def PrimData56.s28 : Seg := ⟨497675238397130228633804515, 497675238397130238071446916, 26984451, 4096, [], 497819801911726017339762976, 497819801911726026780147023⟩
def PrimData56.s29 : Seg := ⟨497819801911726017339762976, 497819801911726026780147023, 26992643, 4096, [], 497978256403510954302719422, 497978256403510963746108537⟩
def PrimData56.s30 : Seg := ⟨497978256403510954302719422, 497978256403510963746108537, 27000835, 4096, [], 498131347650006399872692075, 498131347650006409318984218⟩
def PrimData56.s31 : Seg := ⟨498131347650006399872692075, 498131347650006409318984218, 27009027, 4096, [], 498277181471087274533441160, 498277181471087283982498339⟩
def PrimData56.s32 : Seg := ⟨498277181471087274533441160, 498277181471087283982498339, 27017219, 4096, [], 498433750426851563483659124, 498433750426851572935684498⟩
def PrimData56.s33 : Seg := ⟨498433750426851563483659124, 498433750426851572935684498, 27025411, 4096, [], 498583061781357208076341482, 498583061781357217531198225⟩
def PrimData56.s34 : Seg := ⟨498583061781357208076341482, 498583061781357217531198225, 27033603, 4096, [], 498724483918450097211217876, 498724483918450106668755047⟩

def PrimData56.segs : List Seg := [PrimData56.s0, PrimData56.s1, PrimData56.s2, PrimData56.s3, PrimData56.s4, PrimData56.s5, PrimData56.s6, PrimData56.s7, PrimData56.s8, PrimData56.s9, PrimData56.s10, PrimData56.s11, PrimData56.s12, PrimData56.s13, PrimData56.s14, PrimData56.s15, PrimData56.s16, PrimData56.s17, PrimData56.s18, PrimData56.s19, PrimData56.s20, PrimData56.s21, PrimData56.s22, PrimData56.s23, PrimData56.s24, PrimData56.s25, PrimData56.s26, PrimData56.s27, PrimData56.s28, PrimData56.s29, PrimData56.s30, PrimData56.s31, PrimData56.s32, PrimData56.s33, PrimData56.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked56_s0 : Seg.bok PrimData56.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s0

theorem checked56_s1 : Seg.bok PrimData56.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s1

theorem checked56_s2 : Seg.bok PrimData56.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s2

theorem checked56_s3 : Seg.bok PrimData56.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s3

theorem checked56_s4 : Seg.bok PrimData56.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s4

theorem checked56_s5 : Seg.bok PrimData56.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s5

theorem checked56_s6 : Seg.bok PrimData56.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s6

theorem checked56_s7 : Seg.bok PrimData56.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s7

theorem checked56_s8 : Seg.bok PrimData56.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s8

theorem checked56_s9 : Seg.bok PrimData56.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s9

theorem checked56_s10 : Seg.bok PrimData56.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s10

theorem checked56_s11 : Seg.bok PrimData56.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s11

theorem checked56_s12 : Seg.bok PrimData56.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s12

theorem checked56_s13 : Seg.bok PrimData56.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s13

theorem checked56_s14 : Seg.bok PrimData56.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s14

theorem checked56_s15 : Seg.bok PrimData56.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s15

theorem checked56_s16 : Seg.bok PrimData56.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s16

theorem checked56_s17 : Seg.bok PrimData56.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s17

theorem checked56_s18 : Seg.bok PrimData56.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s18

theorem checked56_s19 : Seg.bok PrimData56.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s19

theorem checked56_s20 : Seg.bok PrimData56.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s20

theorem checked56_s21 : Seg.bok PrimData56.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s21

theorem checked56_s22 : Seg.bok PrimData56.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s22

theorem checked56_s23 : Seg.bok PrimData56.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s23

theorem checked56_s24 : Seg.bok PrimData56.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s24

theorem checked56_s25 : Seg.bok PrimData56.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s25

theorem checked56_s26 : Seg.bok PrimData56.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s26

theorem checked56_s27 : Seg.bok PrimData56.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s27

theorem checked56_s28 : Seg.bok PrimData56.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s28

theorem checked56_s29 : Seg.bok PrimData56.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s29

theorem checked56_s30 : Seg.bok PrimData56.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s30

theorem checked56_s31 : Seg.bok PrimData56.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s31

theorem checked56_s32 : Seg.bok PrimData56.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s32

theorem checked56_s33 : Seg.bok PrimData56.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s33

theorem checked56_s34 : Seg.bok PrimData56.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56_s34

 theorem checked56 : ∀ s ∈ PrimData56.segs, (Seg.bok s) = true := by
  unfold PrimData56.segs
  exact List.forall_mem_cons.2 ⟨checked56_s0, List.forall_mem_cons.2 ⟨checked56_s1, List.forall_mem_cons.2 ⟨checked56_s2, List.forall_mem_cons.2 ⟨checked56_s3, List.forall_mem_cons.2 ⟨checked56_s4, List.forall_mem_cons.2 ⟨checked56_s5, List.forall_mem_cons.2 ⟨checked56_s6, List.forall_mem_cons.2 ⟨checked56_s7, List.forall_mem_cons.2 ⟨checked56_s8, List.forall_mem_cons.2 ⟨checked56_s9, List.forall_mem_cons.2 ⟨checked56_s10, List.forall_mem_cons.2 ⟨checked56_s11, List.forall_mem_cons.2 ⟨checked56_s12, List.forall_mem_cons.2 ⟨checked56_s13, List.forall_mem_cons.2 ⟨checked56_s14, List.forall_mem_cons.2 ⟨checked56_s15, List.forall_mem_cons.2 ⟨checked56_s16, List.forall_mem_cons.2 ⟨checked56_s17, List.forall_mem_cons.2 ⟨checked56_s18, List.forall_mem_cons.2 ⟨checked56_s19, List.forall_mem_cons.2 ⟨checked56_s20, List.forall_mem_cons.2 ⟨checked56_s21, List.forall_mem_cons.2 ⟨checked56_s22, List.forall_mem_cons.2 ⟨checked56_s23, List.forall_mem_cons.2 ⟨checked56_s24, List.forall_mem_cons.2 ⟨checked56_s25, List.forall_mem_cons.2 ⟨checked56_s26, List.forall_mem_cons.2 ⟨checked56_s27, List.forall_mem_cons.2 ⟨checked56_s28, List.forall_mem_cons.2 ⟨checked56_s29, List.forall_mem_cons.2 ⟨checked56_s30, List.forall_mem_cons.2 ⟨checked56_s31, List.forall_mem_cons.2 ⟨checked56_s32, List.forall_mem_cons.2 ⟨checked56_s33, List.forall_mem_singleton.2 checked56_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked56
