/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_65.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/c4fa1597-7516-49eb-970b-aebd8afdb62d
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData65.s0 : Seg := ⟨541035659697993160850536466, 541035659697993171110415113, 29335555, 4096, [], 541179660186224947430076519, 541179660186224957692685398⟩
def PrimData65.s1 : Seg := ⟨541179660186224947430076519, 541179660186224957692685398, 29343747, 4096, [], 541336350439238590262722253, 541336350439238600528302424⟩
def PrimData65.s2 : Seg := ⟨541336350439238590262722253, 541336350439238600528302424, 29351939, 4096, [], 541496849539011288223025993, 541496849539011298491650840⟩
def PrimData65.s3 : Seg := ⟨541496849539011288223025993, 541496849539011298491650840, 29360131, 4096, [], 541645932155532299420843995, 541645932155532309692295321⟩
def PrimData65.s4 : Seg := ⟨541645932155532299420843995, 541645932155532309692295321, 29368323, 4096, [], 541803264494718676883886439, 541803264494718687158321463⟩
def PrimData65.s5 : Seg := ⟨541803264494718676883886439, 541803264494718687158321463, 29376515, 4096, [], 541950448687752087396300742, 541950448687752097673527002⟩
def PrimData65.s6 : Seg := ⟨541950448687752087396300742, 541950448687752097673527002, 29384707, 4096, [], 542094780381296222494104781, 542094780381296232774067372⟩
def PrimData65.s7 : Seg := ⟨542094780381296222494104781, 542094780381296232774067372, 29392899, 4096, [], 542246727618171027761292727, 542246727618171038044136238⟩
def PrimData65.s8 : Seg := ⟨542246727618171027761292727, 542246727618171038044136238, 29401091, 4096, [], 542396773991562745100139276, 542396773991562755385827043⟩
def PrimData65.s9 : Seg := ⟨542396773991562745100139276, 542396773991562755385827043, 29409283, 4096, [], 542544602194026369578776757, 542544602194026379867268412⟩
def PrimData65.s10 : Seg := ⟨542544602194026369578776757, 542544602194026379867268412, 29417475, 4096, [], 542687991542832051596832062, 542687991542832061888042325⟩
def PrimData65.s11 : Seg := ⟨542687991542832051596832062, 542687991542832061888042325, 29425667, 4096, [], 542834555626536646744680199, 542834555626536657038669220⟩
def PrimData65.s12 : Seg := ⟨542834555626536646744680199, 542834555626536657038669220, 29433859, 4096, [], 542988101401062137144042901, 542988101401062147440943494⟩
def PrimData65.s13 : Seg := ⟨542988101401062137144042901, 542988101401062147440943494, 29442051, 4096, [], 543133718462214579067132960, 543133718462214589366794711⟩
def PrimData65.s14 : Seg := ⟨543133718462214579067132960, 543133718462214589366794711, 29450243, 4096, [], 543284413928050341532868324, 543284413928050351835387009⟩
def PrimData65.s15 : Seg := ⟨543284413928050341532868324, 543284413928050351835387009, 29458435, 4096, [], 543430352937558586746681214, 543430352937558597051967138⟩
def PrimData65.s16 : Seg := ⟨543430352937558586746681214, 543430352937558597051967138, 29466627, 4096, [], 543582956817341324856420827, 543582956817341335164599859⟩
def PrimData65.s17 : Seg := ⟨543582956817341324856420827, 543582956817341335164599859, 29474819, 4096, [], 543733659550444251038201685, 543733659550444261349238171⟩
def PrimData65.s18 : Seg := ⟨543733659550444251038201685, 543733659550444261349238171, 29483011, 4096, [], 543891027471781577957443076, 543891027471781588271462971⟩
def PrimData65.s19 : Seg := ⟨543891027471781577957443076, 543891027471781588271462971, 29491203, 4096, [], 544041735085034833594323508, 544041735085034843911202349⟩
def PrimData65.s20 : Seg := ⟨544041735085034833594323508, 544041735085034843911202349, 29499395, 4096, [], 544187685867195763422966151, 544187685867195773742612019⟩
def PrimData65.s21 : Seg := ⟨544187685867195763422966151, 544187685867195773742612019, 29507587, 4096, [], 544338715651962428364693586, 544338715651962438687202386⟩
def PrimData65.s22 : Seg := ⟨544338715651962428364693586, 544338715651962438687202386, 29515779, 4096, [], 544493238110908982002458549, 544493238110908992327898645⟩
def PrimData65.s23 : Seg := ⟨544493238110908982002458549, 544493238110908992327898645, 29523971, 4096, [], 544647763050275310493386801, 544647763050275320821756460⟩
def PrimData65.s24 : Seg := ⟨544647763050275310493386801, 544647763050275320821756460, 29532163, 4096, [], 544805146287184680783403290, 544805146287184691114757305⟩
def PrimData65.s25 : Seg := ⟨544805146287184680783403290, 544805146287184691114757305, 29540355, 4096, [], 544953647408610069488581104, 544953647408610079822750972⟩
def PrimData65.s26 : Seg := ⟨544953647408610069488581104, 544953647408610079822750972, 29548547, 4096, [], 545103420142529618137833398, 545103420142529628474842182⟩
def PrimData65.s27 : Seg := ⟨545103420142529618137833398, 545103420142529628474842182, 29556739, 4096, [], 545246531534506664031361183, 545246531534506674371083130⟩
def PrimData65.s28 : Seg := ⟨545246531534506664031361183, 545246531534506674371083130, 29564931, 4096, [], 545395039752908510731202506, 545395039752908521073740895⟩
def PrimData65.s29 : Seg := ⟨545395039752908510731202506, 545395039752908521073740895, 29573123, 4096, [], 545550214299422590544837427, 545550214299422600890318165⟩
def PrimData65.s30 : Seg := ⟨545550214299422590544837427, 545550214299422600890318165, 29581315, 4096, [], 545699361998629371103976871, 545699361998629381452285367⟩
def PrimData65.s31 : Seg := ⟨545699361998629371103976871, 545699361998629381452285367, 29589507, 4096, [], 545858667001206811492255467, 545858667001206821843584981⟩
def PrimData65.s32 : Seg := ⟨545858667001206811492255467, 545858667001206821843584981, 29597699, 4096, [], 546008771529801104110829488, 546008771529801114465003873⟩
def PrimData65.s33 : Seg := ⟨546008771529801104110829488, 546008771529801114465003873, 29605891, 4096, [], 546156022350923563261907665, 546156022350923573618873675⟩
def PrimData65.s34 : Seg := ⟨546156022350923563261907665, 546156022350923573618873675, 29614083, 4096, [], 546314065634793531960823446, 546314065634793542320786848⟩

def PrimData65.segs : List Seg := [PrimData65.s0, PrimData65.s1, PrimData65.s2, PrimData65.s3, PrimData65.s4, PrimData65.s5, PrimData65.s6, PrimData65.s7, PrimData65.s8, PrimData65.s9, PrimData65.s10, PrimData65.s11, PrimData65.s12, PrimData65.s13, PrimData65.s14, PrimData65.s15, PrimData65.s16, PrimData65.s17, PrimData65.s18, PrimData65.s19, PrimData65.s20, PrimData65.s21, PrimData65.s22, PrimData65.s23, PrimData65.s24, PrimData65.s25, PrimData65.s26, PrimData65.s27, PrimData65.s28, PrimData65.s29, PrimData65.s30, PrimData65.s31, PrimData65.s32, PrimData65.s33, PrimData65.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked65_s0 : Seg.bok PrimData65.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s0

theorem checked65_s1 : Seg.bok PrimData65.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s1

theorem checked65_s2 : Seg.bok PrimData65.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s2

theorem checked65_s3 : Seg.bok PrimData65.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s3

theorem checked65_s4 : Seg.bok PrimData65.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s4

theorem checked65_s5 : Seg.bok PrimData65.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s5

theorem checked65_s6 : Seg.bok PrimData65.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s6

theorem checked65_s7 : Seg.bok PrimData65.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s7

theorem checked65_s8 : Seg.bok PrimData65.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s8

theorem checked65_s9 : Seg.bok PrimData65.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s9

theorem checked65_s10 : Seg.bok PrimData65.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s10

theorem checked65_s11 : Seg.bok PrimData65.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s11

theorem checked65_s12 : Seg.bok PrimData65.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s12

theorem checked65_s13 : Seg.bok PrimData65.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s13

theorem checked65_s14 : Seg.bok PrimData65.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s14

theorem checked65_s15 : Seg.bok PrimData65.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s15

theorem checked65_s16 : Seg.bok PrimData65.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s16

theorem checked65_s17 : Seg.bok PrimData65.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s17

theorem checked65_s18 : Seg.bok PrimData65.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s18

theorem checked65_s19 : Seg.bok PrimData65.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s19

theorem checked65_s20 : Seg.bok PrimData65.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s20

theorem checked65_s21 : Seg.bok PrimData65.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s21

theorem checked65_s22 : Seg.bok PrimData65.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s22

theorem checked65_s23 : Seg.bok PrimData65.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s23

theorem checked65_s24 : Seg.bok PrimData65.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s24

theorem checked65_s25 : Seg.bok PrimData65.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s25

theorem checked65_s26 : Seg.bok PrimData65.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s26

theorem checked65_s27 : Seg.bok PrimData65.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s27

theorem checked65_s28 : Seg.bok PrimData65.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s28

theorem checked65_s29 : Seg.bok PrimData65.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s29

theorem checked65_s30 : Seg.bok PrimData65.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s30

theorem checked65_s31 : Seg.bok PrimData65.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s31

theorem checked65_s32 : Seg.bok PrimData65.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s32

theorem checked65_s33 : Seg.bok PrimData65.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s33

theorem checked65_s34 : Seg.bok PrimData65.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65_s34

 theorem checked65 : ∀ s ∈ PrimData65.segs, (Seg.bok s) = true := by
  unfold PrimData65.segs
  exact List.forall_mem_cons.2 ⟨checked65_s0, List.forall_mem_cons.2 ⟨checked65_s1, List.forall_mem_cons.2 ⟨checked65_s2, List.forall_mem_cons.2 ⟨checked65_s3, List.forall_mem_cons.2 ⟨checked65_s4, List.forall_mem_cons.2 ⟨checked65_s5, List.forall_mem_cons.2 ⟨checked65_s6, List.forall_mem_cons.2 ⟨checked65_s7, List.forall_mem_cons.2 ⟨checked65_s8, List.forall_mem_cons.2 ⟨checked65_s9, List.forall_mem_cons.2 ⟨checked65_s10, List.forall_mem_cons.2 ⟨checked65_s11, List.forall_mem_cons.2 ⟨checked65_s12, List.forall_mem_cons.2 ⟨checked65_s13, List.forall_mem_cons.2 ⟨checked65_s14, List.forall_mem_cons.2 ⟨checked65_s15, List.forall_mem_cons.2 ⟨checked65_s16, List.forall_mem_cons.2 ⟨checked65_s17, List.forall_mem_cons.2 ⟨checked65_s18, List.forall_mem_cons.2 ⟨checked65_s19, List.forall_mem_cons.2 ⟨checked65_s20, List.forall_mem_cons.2 ⟨checked65_s21, List.forall_mem_cons.2 ⟨checked65_s22, List.forall_mem_cons.2 ⟨checked65_s23, List.forall_mem_cons.2 ⟨checked65_s24, List.forall_mem_cons.2 ⟨checked65_s25, List.forall_mem_cons.2 ⟨checked65_s26, List.forall_mem_cons.2 ⟨checked65_s27, List.forall_mem_cons.2 ⟨checked65_s28, List.forall_mem_cons.2 ⟨checked65_s29, List.forall_mem_cons.2 ⟨checked65_s30, List.forall_mem_cons.2 ⟨checked65_s31, List.forall_mem_cons.2 ⟨checked65_s32, List.forall_mem_cons.2 ⟨checked65_s33, List.forall_mem_singleton.2 checked65_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked65
