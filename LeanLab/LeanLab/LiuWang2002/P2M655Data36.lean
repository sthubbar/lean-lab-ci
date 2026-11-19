/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_36.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/bff72ca8-d9bd-401e-ac4d-d9c5d3b31f6f
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData36.s0 : Seg := ⟨387681220992923415775547678, 387681220992923423127302246, 21020675, 4096, [], 387831761698439494947247712, 387831761698439502301855367⟩
def PrimData36.s1 : Seg := ⟨387831761698439494947247712, 387831761698439502301855367, 21028867, 4096, [], 387979817587303644151818408, 387979817587303651509232273⟩
def PrimData36.s2 : Seg := ⟨387979817587303644151818408, 387979817587303651509232273, 21037059, 4096, [], 388132542547759676446924071, 388132542547759683807234106⟩
def PrimData36.s3 : Seg := ⟨388132542547759676446924071, 388132542547759683807234106, 21045251, 4096, [], 388283715782124627895480737, 388283715782124635258656917⟩
def PrimData36.s4 : Seg := ⟨388283715782124627895480737, 388283715782124635258656917, 21053443, 4096, [], 388438003111018326584097405, 388438003111018333950197994⟩
def PrimData36.s5 : Seg := ⟨388438003111018326584097405, 388438003111018333950197994, 21061635, 4096, [], 388585139347223727906917351, 388585139347223735275807127⟩
def PrimData36.s6 : Seg := ⟨388585139347223727906917351, 388585139347223735275807127, 21069827, 4096, [], 388735700863681437884452902, 388735700863681445256196912⟩
def PrimData36.s7 : Seg := ⟨388735700863681437884452902, 388735700863681445256196912, 21078019, 4096, [], 388884710459009036200935338, 388884710459009043575504776⟩
def PrimData36.s8 : Seg := ⟨388884710459009036200935338, 388884710459009043575504776, 21086211, 4096, [], 389029990335824306856024678, 389029990335824314233348670⟩
def PrimData36.s9 : Seg := ⟨389029990335824306856024678, 389029990335824314233348670, 21094403, 4096, [], 389182739988263823759000656, 389182739988263831139221251⟩
def PrimData36.s10 : Seg := ⟨389182739988263823759000656, 389182739988263831139221251, 21102595, 4096, [], 389331137589751910918068539, 389331137589751918301103450⟩
def PrimData36.s11 : Seg := ⟨389331137589751910918068539, 389331137589751918301103450, 21110787, 4096, [], 389484516490451271868576862, 389484516490451279254520894⟩
def PrimData36.s12 : Seg := ⟨389484516490451271868576862, 389484516490451279254520894, 21118979, 4096, [], 389637587722616938634229282, 389637587722616946023076685⟩
def PrimData36.s13 : Seg := ⟨389637587722616938634229282, 389637587722616946023076685, 21127171, 4096, [], 389786928980997776204546306, 389786928980997783596227050⟩
def PrimData36.s14 : Seg := ⟨389786928980997776204546306, 389786928980997783596227050, 21135363, 4096, [], 389941251842285163469852254, 389941251842285170864461591⟩
def PrimData36.s15 : Seg := ⟨389941251842285163469852254, 389941251842285170864461591, 21143555, 4096, [], 390091222234053499017106168, 390091222234053506414561880⟩
def PrimData36.s16 : Seg := ⟨390091222234053499017106168, 390091222234053506414561880, 21151747, 4096, [], 390232795081400453108091567, 390232795081400460508234003⟩
def PrimData36.s17 : Seg := ⟨390232795081400453108091567, 390232795081400460508234003, 21159939, 4096, [], 390381216664497931392592766, 390381216664497938795551931⟩
def PrimData36.s18 : Seg := ⟨390381216664497931392592766, 390381216664497938795551931, 21168131, 4096, [], 390535864814976204086463954, 390535864814976211492359161⟩
def PrimData36.s19 : Seg := ⟨390535864814976204086463954, 390535864814976211492359161, 21176323, 4096, [], 390687715963534318511160139, 390687715963534325919936713⟩
def PrimData36.s20 : Seg := ⟨390687715963534318511160139, 390687715963534325919936713, 21184515, 4096, [], 390835836564371857224244778, 390835836564371864635832249⟩
def PrimData36.s21 : Seg := ⟨390835836564371857224244778, 390835836564371864635832249, 21192707, 4096, [], 390988317088232224064284257, 390988317088232231478765245⟩
def PrimData36.s22 : Seg := ⟨390988317088232224064284257, 390988317088232231478765245, 21200899, 4096, [], 391139245163911073345260807, 391139245163911080762605909⟩
def PrimData36.s23 : Seg := ⟨391139245163911073345260807, 391139245163911080762605909, 21209091, 4096, [], 391286753550599893164700772, 391286753550599900584844378⟩
def PrimData36.s24 : Seg := ⟨391286753550599893164700772, 391286753550599900584844378, 21217283, 4096, [], 391433642863935061662264208, 391433642863935069085194897⟩
def PrimData36.s25 : Seg := ⟨391433642863935061662264208, 391433642863935069085194897, 21225475, 4096, [], 391583336459023564137146071, 391583336459023571562916817⟩
def PrimData36.s26 : Seg := ⟨391583336459023564137146071, 391583336459023571562916817, 21233667, 4096, [], 391732411037281151493911067, 391732411037281158922511178⟩
def PrimData36.s27 : Seg := ⟨391732411037281151493911067, 391732411037281158922511178, 21241859, 4096, [], 391883045183514081072797902, 391883045183514088504255809⟩
def PrimData36.s28 : Seg := ⟨391883045183514081072797902, 391883045183514088504255809, 21250051, 4096, [], 392034927664754925163597031, 392034927664754932597936305⟩
def PrimData36.s29 : Seg := ⟨392034927664754925163597031, 392034927664754932597936305, 21258243, 4096, [], 392191793496636404290245649, 392191793496636411727560331⟩
def PrimData36.s30 : Seg := ⟨392191793496636404290245649, 392191793496636411727560331, 21266435, 4096, [], 392347729195869051285208510, 392347729195869058725481104⟩
def PrimData36.s31 : Seg := ⟨392347729195869051285208510, 392347729195869058725481104, 21274627, 4096, [], 392504913430782038745646313, 392504913430782046188901362⟩
def PrimData36.s32 : Seg := ⟨392504913430782038745646313, 392504913430782046188901362, 21282819, 4096, [], 392658054835881950339618110, 392658054835881957785779069⟩
def PrimData36.s33 : Seg := ⟨392658054835881950339618110, 392658054835881957785779069, 21291011, 4096, [], 392811199765595205956294953, 392811199765595213405362065⟩
def PrimData36.s34 : Seg := ⟨392811199765595205956294953, 392811199765595213405362065, 21299203, 4096, [], 392958433869354890047363211, 392958433869354897499222995⟩

def PrimData36.segs : List Seg := [PrimData36.s0, PrimData36.s1, PrimData36.s2, PrimData36.s3, PrimData36.s4, PrimData36.s5, PrimData36.s6, PrimData36.s7, PrimData36.s8, PrimData36.s9, PrimData36.s10, PrimData36.s11, PrimData36.s12, PrimData36.s13, PrimData36.s14, PrimData36.s15, PrimData36.s16, PrimData36.s17, PrimData36.s18, PrimData36.s19, PrimData36.s20, PrimData36.s21, PrimData36.s22, PrimData36.s23, PrimData36.s24, PrimData36.s25, PrimData36.s26, PrimData36.s27, PrimData36.s28, PrimData36.s29, PrimData36.s30, PrimData36.s31, PrimData36.s32, PrimData36.s33, PrimData36.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked36_s0 : Seg.bok PrimData36.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s0

theorem checked36_s1 : Seg.bok PrimData36.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s1

theorem checked36_s2 : Seg.bok PrimData36.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s2

theorem checked36_s3 : Seg.bok PrimData36.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s3

theorem checked36_s4 : Seg.bok PrimData36.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s4

theorem checked36_s5 : Seg.bok PrimData36.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s5

theorem checked36_s6 : Seg.bok PrimData36.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s6

theorem checked36_s7 : Seg.bok PrimData36.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s7

theorem checked36_s8 : Seg.bok PrimData36.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s8

theorem checked36_s9 : Seg.bok PrimData36.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s9

theorem checked36_s10 : Seg.bok PrimData36.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s10

theorem checked36_s11 : Seg.bok PrimData36.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s11

theorem checked36_s12 : Seg.bok PrimData36.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s12

theorem checked36_s13 : Seg.bok PrimData36.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s13

theorem checked36_s14 : Seg.bok PrimData36.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s14

theorem checked36_s15 : Seg.bok PrimData36.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s15

theorem checked36_s16 : Seg.bok PrimData36.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s16

theorem checked36_s17 : Seg.bok PrimData36.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s17

theorem checked36_s18 : Seg.bok PrimData36.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s18

theorem checked36_s19 : Seg.bok PrimData36.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s19

theorem checked36_s20 : Seg.bok PrimData36.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s20

theorem checked36_s21 : Seg.bok PrimData36.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s21

theorem checked36_s22 : Seg.bok PrimData36.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s22

theorem checked36_s23 : Seg.bok PrimData36.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s23

theorem checked36_s24 : Seg.bok PrimData36.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s24

theorem checked36_s25 : Seg.bok PrimData36.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s25

theorem checked36_s26 : Seg.bok PrimData36.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s26

theorem checked36_s27 : Seg.bok PrimData36.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s27

theorem checked36_s28 : Seg.bok PrimData36.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s28

theorem checked36_s29 : Seg.bok PrimData36.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s29

theorem checked36_s30 : Seg.bok PrimData36.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s30

theorem checked36_s31 : Seg.bok PrimData36.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s31

theorem checked36_s32 : Seg.bok PrimData36.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s32

theorem checked36_s33 : Seg.bok PrimData36.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s33

theorem checked36_s34 : Seg.bok PrimData36.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36_s34

 theorem checked36 : ∀ s ∈ PrimData36.segs, (Seg.bok s) = true := by
  unfold PrimData36.segs
  exact List.forall_mem_cons.2 ⟨checked36_s0, List.forall_mem_cons.2 ⟨checked36_s1, List.forall_mem_cons.2 ⟨checked36_s2, List.forall_mem_cons.2 ⟨checked36_s3, List.forall_mem_cons.2 ⟨checked36_s4, List.forall_mem_cons.2 ⟨checked36_s5, List.forall_mem_cons.2 ⟨checked36_s6, List.forall_mem_cons.2 ⟨checked36_s7, List.forall_mem_cons.2 ⟨checked36_s8, List.forall_mem_cons.2 ⟨checked36_s9, List.forall_mem_cons.2 ⟨checked36_s10, List.forall_mem_cons.2 ⟨checked36_s11, List.forall_mem_cons.2 ⟨checked36_s12, List.forall_mem_cons.2 ⟨checked36_s13, List.forall_mem_cons.2 ⟨checked36_s14, List.forall_mem_cons.2 ⟨checked36_s15, List.forall_mem_cons.2 ⟨checked36_s16, List.forall_mem_cons.2 ⟨checked36_s17, List.forall_mem_cons.2 ⟨checked36_s18, List.forall_mem_cons.2 ⟨checked36_s19, List.forall_mem_cons.2 ⟨checked36_s20, List.forall_mem_cons.2 ⟨checked36_s21, List.forall_mem_cons.2 ⟨checked36_s22, List.forall_mem_cons.2 ⟨checked36_s23, List.forall_mem_cons.2 ⟨checked36_s24, List.forall_mem_cons.2 ⟨checked36_s25, List.forall_mem_cons.2 ⟨checked36_s26, List.forall_mem_cons.2 ⟨checked36_s27, List.forall_mem_cons.2 ⟨checked36_s28, List.forall_mem_cons.2 ⟨checked36_s29, List.forall_mem_cons.2 ⟨checked36_s30, List.forall_mem_cons.2 ⟨checked36_s31, List.forall_mem_cons.2 ⟨checked36_s32, List.forall_mem_cons.2 ⟨checked36_s33, List.forall_mem_singleton.2 checked36_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked36
